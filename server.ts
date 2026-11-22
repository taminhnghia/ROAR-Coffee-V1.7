import 'dotenv/config';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { createServer as createHttpServer } from 'node:http';
import express from 'express';
import { createServer as createViteServer } from 'vite';
import {
  ADMIN_ROLE_PRESETS,
  ALL_ADMIN_PERMISSIONS,
  attachAuth,
  type AuthedRequest,
  hashPassword,
  requireAdmin,
  requireAuth,
  resolveEffectiveAdminPermissions,
  SESSION_COOKIE_NAME,
  signSessionToken,
  verifyPassword,
} from './server/auth.ts';
import { db, initDatabase, logAudit } from './server/db.ts';
import { dispatchB2BInquiryEmail, dispatchOrderConfirmationEmail } from './server/mailer.ts';
import { buildLiveShippingTracking } from './src/lib/shippingTracking.ts';
import {
  buildCmsSnapshot,
  exportCmsSnapshotToDisk,
  restoreFromSnapshot,
  scheduleSnapshotSync,
} from './server/snapshot.ts';
import {
  convertVndToUsdByRate,
  getVietcombankUsdRate,
  type VcbRateMode,
} from './server/vietcombank.ts';
import {
  chatWithRoarBarista,
  GeminiTranslationError,
  translateProductViToEn,
} from './server/gemini.ts';
import {
  calculateShippingFee,
  generateEan13Barcode,
  normalizeVolumeTiers,
  resolveVolumeTier,
} from './src/lib/pricing.ts';
import {
  normalizeMembershipTierName,
  resolveEffectiveMembershipTier,
} from './src/lib/membershipTiers.ts';

initDatabase();

const app = express();
const IS_PROD = process.env.NODE_ENV === 'production';
const portArgIdx = process.argv.indexOf('--port');
const cliPort = portArgIdx >= 0 ? Number(process.argv[portArgIdx + 1]) : NaN;
const envPort = Number(process.env.PORT);
const PORT =
  Number.isFinite(cliPort) && cliPort > 0
    ? cliPort
    : !IS_PROD && envPort === 8080
      ? 3000
      : envPort || 3000;
const UPLOADS_DIR = path.resolve(process.cwd(), 'public/uploads');
fs.mkdirSync(UPLOADS_DIR, { recursive: true });

app.set('trust proxy', 1);
app.use(express.json({ limit: '10mb' }));
app.use('/uploads', express.static(UPLOADS_DIR));
app.use(attachAuth);

function isHttpsRequest(req: express.Request): boolean {
  const xfProto = req.headers['x-forwarded-proto'];
  if (typeof xfProto === 'string' && xfProto.includes('https')) return true;
  return Boolean(req.secure || IS_PROD);
}

function setSessionCookie(req: express.Request, res: express.Response, token: string): void {
  const https = isHttpsRequest(req);
  res.cookie(SESSION_COOKIE_NAME, token, {
    httpOnly: true,
    sameSite: https ? 'none' : 'lax',
    secure: https,
    maxAge: 1000 * 60 * 60 * 24 * 7,
    path: '/',
  });
}

function getPointsSummary(userId: number) {
  const rows = db
    .prepare('SELECT entry_type, points, expires_at FROM points_ledger WHERE user_id = ?')
    .all(userId) as Array<{ entry_type: string; points: number; expires_at: string | null }>;

  let available = 0;
  let pending = 0;
  let redeemed = 0;
  let expired = 0;
  let expiringSoon = 0;
  const thirtyDaysOut = Date.now() + 30 * 24 * 60 * 60 * 1000;

  for (const r of rows) {
    if (r.entry_type === 'earn_available' || r.entry_type === 'admin_adjustment') {
      available += r.points;
      if (r.expires_at && new Date(r.expires_at).getTime() <= thirtyDaysOut && r.points > 0) {
        expiringSoon += r.points;
      }
    } else if (r.entry_type === 'earn_pending') {
      pending += r.points;
    } else if (r.entry_type === 'redeem') {
      redeemed += Math.abs(r.points);
      available -= Math.abs(r.points);
    } else if (r.entry_type === 'reverse') {
      available -= Math.abs(r.points);
    } else if (r.entry_type === 'expire') {
      expired += Math.abs(r.points);
      available -= Math.abs(r.points);
    }
  }

  return {
    available: Math.max(0, available),
    pending: Math.max(0, pending),
    redeemed,
    expired,
    expiringSoon: Math.min(Math.max(0, available), expiringSoon),
  };
}

function syncUserTierInDb(userId: number): string {
  const row = db
    .prepare('SELECT id, email, phone, tier FROM users WHERE id = ?')
    .get(userId) as { id: number; email: string; phone: string; tier: string } | undefined;
  if (!row) return 'ROAR Member';
  const pts = getPointsSummary(userId);
  const stats = db
    .prepare(
      "SELECT COALESCE(SUM(total), 0) as spent FROM orders WHERE (user_id = ? OR LOWER(TRIM(customer_email)) = LOWER(TRIM(?))) AND order_status != 'Cancelled'"
    )
    .get(userId, row.email || '') as { spent: number };
  const effective = resolveEffectiveMembershipTier({
    currentTierName: row.tier,
    lifetimeSpendVnd: Number(stats?.spent || 0),
    lifetimePoints: pts.available + pts.redeemed,
  }).tier.name;
  if (effective !== row.tier) {
    db.prepare('UPDATE users SET tier = ? WHERE id = ?').run(effective, userId);
  }
  return effective;
}

function createUserNotification(
  userId: number | null | undefined,
  opts: {
    titleVi: string;
    titleEn: string;
    messageVi: string;
    messageEn: string;
    category: 'order' | 'promo' | 'loyalty' | 'system';
    linkUrl?: string;
  }
): void {
  if (!userId) return;
  db.prepare(`
    INSERT INTO user_notifications (user_id, title_vi, title_en, message_vi, message_en, category, link_url)
    VALUES (?, ?, ?, ?, ?, ?, ?)
  `).run(
    userId,
    opts.titleVi,
    opts.titleEn,
    opts.messageVi,
    opts.messageEn,
    opts.category,
    opts.linkUrl || '/account'
  );
}

function requirePermission(...allowedPerms: string[]) {
  return (req: AuthedRequest, res: express.Response, next: express.NextFunction): void => {
    if (!req.authUser) {
      res.status(401).json({ error: 'Administrator authentication required' });
      return;
    }
    const dbUser = db
      .prepare('SELECT id, email, role, admin_role, admin_permissions_json FROM users WHERE id = ?')
      .get(req.authUser.userId) as any;
    if (!dbUser || dbUser.role !== 'admin') {
      res.status(403).json({ error: 'Forbidden: Administrator role required' });
      return;
    }
    const { adminRole, adminPermissions } = resolveEffectiveAdminPermissions(dbUser);
    if (adminRole === 'super_admin') {
      next();
      return;
    }
    const permitted = allowedPerms.some((p) => adminPermissions.includes(p));
    if (!permitted) {
      res.status(403).json({
        error: `Tài khoản quản trị chưa được cấp quyền cho phân hệ (${allowedPerms.join(' / ')}).`,
      });
      return;
    }
    next();
  };
}

// ---------- SEO ROUTES ----------
app.get('/robots.txt', (_req, res) => {
  res.type('text/plain').send(
    [
      'User-agent: *',
      'Allow: /',
      'Disallow: /admin',
      'Disallow: /api/',
      `Sitemap: ${process.env.APP_URL || ''}/sitemap.xml`,
    ].join('\n')
  );
});

app.get('/sitemap.xml', (_req, res) => {
  const baseUrl = (process.env.APP_URL || '').replace(/\/$/, '');
  const staticPaths = [
    '',
    '/shop',
    '/coffee/roasted',
    '/coffee/green-beans',
    '/coffee/instant',
    '/personalities',
    '/origins',
    '/farm-to-cup',
    '/brewing',
    '/about',
    '/signature-reserve',
    '/promotions',
    '/partners',
    '/oem-export',
    '/farm-membership',
    '/journal',
    '/contact',
  ];
  const products = db.prepare("SELECT slug FROM products WHERE status != 'draft'").all() as Array<{ slug: string }>;
  const articles = db.prepare('SELECT slug FROM journal_articles WHERE published = 1').all() as Array<{ slug: string }>;
  const personalities = db.prepare('SELECT slug FROM personalities').all() as Array<{ slug: string }>;

  const allPaths = [
    ...staticPaths,
    ...products.map((p) => `/product/${p.slug}`),
    ...articles.map((a) => `/journal/${a.slug}`),
    ...personalities.map((p) => `/personalities/${p.slug}`),
  ];

  const urls = allPaths
    .flatMap((p) => [
      `  <url><loc>${baseUrl}${p || '/'}</loc><xhtml:link rel="alternate" hreflang="vi" href="${baseUrl}${p || '/'}"/><xhtml:link rel="alternate" hreflang="en" href="${baseUrl}/en${p}"/></url>`,
      `  <url><loc>${baseUrl}/en${p}</loc><xhtml:link rel="alternate" hreflang="vi" href="${baseUrl}${p || '/'}"/><xhtml:link rel="alternate" hreflang="en" href="${baseUrl}/en${p}"/></url>`,
    ])
    .join('\n');

  res.type('application/xml').send(
    `<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9" xmlns:xhtml="http://www.w3.org/1999/xhtml">\n${urls}\n</urlset>`
  );
});

// ---------- AUTH ROUTES ----------
app.post('/api/auth/register', (req, res) => {
  const { email, password, fullName, phone, roleIntent, companyName } = req.body || {};
  if (!email || !password || !fullName) {
    res.status(400).json({ error: 'Missing required registration fields' });
    return;
  }
  if (typeof password !== 'string' || password.length < 8) {
    res.status(400).json({ error: 'Password must be at least 8 characters' });
    return;
  }
  const normalizedEmail = String(email).trim().toLowerCase();
  const existing = db.prepare('SELECT id FROM users WHERE email = ?').get(normalizedEmail);
  if (existing) {
    res.status(409).json({ error: 'Email already registered' });
    return;
  }

  const role = roleIntent === 'b2b_partner' ? 'b2b_partner' : 'customer';
  const memberCode = `RC-${role === 'b2b_partner' ? 'B2B' : 'MEM'}-${Math.floor(100000 + Math.random() * 900000)}`;
  const verificationToken = crypto.randomBytes(16).toString('hex');

  const result = db
    .prepare(`
      INSERT INTO users (email, password_hash, full_name, phone, role, member_code, tier, email_verified, verification_token, company_name)
      VALUES (?, ?, ?, ?, ?, ?, 'ROAR Member', 0, ?, ?)
    `)
    .run(
      normalizedEmail,
      hashPassword(password),
      String(fullName).trim(),
      String(phone || '').trim(),
      role,
      memberCode,
      verificationToken,
      String(companyName || '').trim()
    );

  const userId = Number(result.lastInsertRowid);
  const welcomePts = 50;
  db.prepare(`
    INSERT INTO points_ledger (user_id, entry_type, points, description_vi, description_en)
    VALUES (?, 'earn_available', ?, ?, ?)
  `).run(
    userId,
    welcomePts,
    'Quà chào mừng thành viên mới đăng ký ROAR COFFEE®',
    'Welcome bonus points on ROAR COFFEE® member registration'
  );
  createUserNotification(userId, {
    titleVi: `Chào mừng ${String(fullName).trim()} gia nhập ROAR CLUB!`,
    titleEn: `Welcome ${String(fullName).trim()} to ROAR CLUB!`,
    messageVi: `Tài khoản thành viên ${memberCode} đã được ghi nhận vào hệ thống kèm ${welcomePts} điểm thưởng chào mừng.`,
    messageEn: `Your member account (${memberCode}) is registered with ${welcomePts} welcome reward points.`,
    category: 'loyalty',
    linkUrl: '/account?tab=rewards',
  });

  const token = signSessionToken({ userId, email: normalizedEmail, role });
  setSessionCookie(req, res, token);

  res.status(201).json({
    token,
    user: {
      id: userId,
      email: normalizedEmail,
      fullName: String(fullName).trim(),
      phone: String(phone || '').trim(),
      role,
      memberCode,
      tier: 'ROAR Member',
      emailVerified: false,
      verificationTokenPreview: verificationToken,
      points: { available: welcomePts, pending: 0, redeemed: 0, expired: 0, expiringSoon: 0 },
      walletBalanceVnd: 0,
    },
  });
});

app.post('/api/auth/login', (req, res) => {
  const { email, password } = req.body || {};
  if (!email || !password) {
    res.status(400).json({ error: 'Email and password are required' });
    return;
  }
  const normalizedEmail = String(email).trim().toLowerCase();
  const user = db.prepare('SELECT * FROM users WHERE email = ?').get(normalizedEmail) as any;
  if (user && user.role === 'admin' && !String(user.password_hash || '').includes(':')) {
    res.status(401).json({
      code: 'PASSWORD_NOT_SET',
      error:
        'Tài khoản Quản trị viên này chưa được đặt mật khẩu trên hệ thống hiện tại. Vui lòng đăng nhập Super Admin khác để đặt mật khẩu tại mục Phân quyền Thành viên.',
    });
    return;
  }
  if (!user || !verifyPassword(String(password), user.password_hash)) {
    res.status(401).json({ error: 'Invalid email or password' });
    return;
  }

  const syncedTier = syncUserTierInDb(user.id);
  const token = signSessionToken({ userId: user.id, email: user.email, role: user.role });
  setSessionCookie(req, res, token);
  const rbac = resolveEffectiveAdminPermissions(user);

  res.json({
    token,
    user: {
      id: user.id,
      email: user.email,
      fullName: user.full_name,
      phone: user.phone,
      role: user.role,
      adminRole: rbac.adminRole,
      adminPermissions: rbac.adminPermissions,
      memberCode: user.member_code,
      tier: syncedTier,
      emailVerified: Boolean(user.email_verified),
      companyName: user.company_name,
      b2bVerified: Boolean(user.b2b_verified),
    },
  });
});

app.post('/api/auth/social', (req, res) => {
  const { provider, email, fullName } = req.body || {};
  const cleanProvider = String(provider || 'google').toLowerCase();
  const normalizedEmail = String(email || '').trim().toLowerCase();
  const cleanName = String(fullName || '').trim() || (normalizedEmail ? normalizedEmail.split('@')[0] : 'ROAR Member');

  if (!normalizedEmail || !normalizedEmail.includes('@')) {
    res.status(400).json({ error: 'Vui lòng cung cấp email tài khoản hợp lệ.' });
    return;
  }

  let user = db.prepare('SELECT * FROM users WHERE email = ?').get(normalizedEmail) as any;
  if (!user) {
    const memberCode = `RC-MEM-${Math.floor(100000 + Math.random() * 900000)}`;
    const randomPass = crypto.randomBytes(16).toString('hex');
    const result = db
      .prepare(`
        INSERT INTO users (email, password_hash, full_name, phone, role, member_code, tier, email_verified)
        VALUES (?, ?, ?, '', 'customer', ?, 'ROAR Member', 1)
      `)
      .run(normalizedEmail, hashPassword(randomPass), cleanName, memberCode);
    const newId = Number(result.lastInsertRowid);
    db.prepare(`
      INSERT INTO points_ledger (user_id, entry_type, points, description_vi, description_en)
      VALUES (?, 'earn_available', 50, ?, ?)
    `).run(
      newId,
      `Quà chào mừng đăng ký qua ${cleanProvider.toUpperCase()}`,
      `Welcome bonus via ${cleanProvider.toUpperCase()} sign-in`
    );
    createUserNotification(newId, {
      titleVi: `Chào mừng ${cleanName} gia nhập ROAR COFFEE®`,
      titleEn: `Welcome ${cleanName} to ROAR COFFEE®`,
      messageVi: `Tài khoản liên kết ${cleanProvider.toUpperCase()} đã được kích hoạt kèm 50 điểm thưởng chào mừng.`,
      messageEn: `Your ${cleanProvider.toUpperCase()} account is active with 50 welcome reward points.`,
      category: 'loyalty',
      linkUrl: '/account?tab=rewards',
    });
    user = db.prepare('SELECT * FROM users WHERE id = ?').get(newId) as any;
  }

  const syncedTier = syncUserTierInDb(user.id);
  const token = signSessionToken({ userId: user.id, email: user.email, role: user.role });
  setSessionCookie(req, res, token);
  const rbac = resolveEffectiveAdminPermissions(user);

  res.json({
    ok: true,
    token,
    user: {
      id: user.id,
      email: user.email,
      fullName: user.full_name,
      phone: user.phone,
      role: user.role,
      adminRole: rbac.adminRole,
      adminPermissions: rbac.adminPermissions,
      memberCode: user.member_code,
      tier: syncedTier,
      emailVerified: Boolean(user.email_verified),
      companyName: user.company_name,
      b2bVerified: Boolean(user.b2b_verified),
    },
  });
});

app.post('/api/ai/chat', async (req, res) => {
  const { message, history = [], lang = 'vi' } = req.body || {};
  const cleanMsg = String(message || '').trim();
  if (!cleanMsg) {
    res.status(400).json({ error: 'Message is required' });
    return;
  }

  const allProducts = db
    .prepare(
      "SELECT id, slug, sku, sub_category, category, name_vi, name_en, price_vnd, price_usd, image_key, tasting_notes_vi, tasting_notes_en, roast_profile_vi, pricing_tiers_json, variants_json FROM products WHERE status != 'draft'"
    )
    .all() as any[];

  const hydrateProductCard = (p: any) => ({
    id: p.id,
    slug: p.slug,
    sku: p.sku,
    sub_category: p.sub_category || '',
    category: p.category,
    name_vi: p.name_vi,
    name_en: p.name_en,
    price_vnd: p.price_vnd,
    price_usd: p.price_usd,
    image_key: p.image_key,
    tasting_notes_vi: p.tasting_notes_vi || '',
    tasting_notes_en: p.tasting_notes_en || '',
    pricing_tiers: JSON.parse(p.pricing_tiers_json || '[]'),
    variants: JSON.parse(p.variants_json || '[]'),
    to: `/product/${p.slug}`,
  });

  const activePromos = db
    .prepare("SELECT code, title_vi, discount_type, discount_value, min_order_value FROM promotions WHERE active = 1 LIMIT 6")
    .all() as any[];

  const catalogLines = allProducts
    .filter((p) => p.category !== 'green_bean')
    .map((p) => {
      const tiers = JSON.parse(p.pricing_tiers_json || '[]');
      const tierStr =
        Array.isArray(tiers) && tiers.length > 0
          ? ` | 5-tier kg: ${tiers.map((t: any) => `${t.labelVi}=${Number(t.priceVnd).toLocaleString('vi-VN')}₫/kg`).join(', ')}`
          : ` | ${Number(p.price_vnd || 0).toLocaleString('vi-VN')}₫`;
      return `- slug="${p.slug}" | ${p.sku}${p.sub_category ? ` (${p.sub_category})` : ''} | ${p.name_vi} [${p.category}]${tierStr} | Gu vị: ${p.tasting_notes_vi || p.roast_profile_vi}`;
    })
    .join('\n');

  const siteRows = db.prepare('SELECT key, value FROM site_settings').all() as Array<{ key: string; value: string }>;
  const siteMap: Record<string, string> = {};
  for (const r of siteRows) siteMap[r.key] = r.value;

  const hotline = siteMap.hotline || siteMap.contact_phone || '0901234567';
  const zaloPhone = siteMap.zalo_phone || hotline;
  const contactEmail = siteMap.contact_email || 'hello@roarcoffee.vn';
  const b2bEmail = siteMap.b2b_email || 'b2b@roarcoffee.vn';
  const addressVi = siteMap.office_address_vi || 'TP. Hồ Chí Minh & Xưởng rang Tây Nguyên (Đắk Lắk / Lâm Đồng), Việt Nam';
  const addressEn = siteMap.office_address_en || 'Ho Chi Minh City & Central Highlands Roastery (Dak Lak / Lam Dong), Vietnam';
  const openHoursVi = '08:00 – 17:30 (Thứ 2 – Thứ 7, nghỉ Chủ nhật & ngày lễ). Tư vấn Zalo & AI Barista hỗ trợ 24/7.';
  const openHoursEn = '08:00 – 17:30 (Monday – Saturday, closed Sunday & public holidays). Zalo & AI Barista available 24/7.';

  const promoLines = activePromos
    .map((pr) => `- Voucher ${pr.code}: ${pr.title_vi} (tối thiểu ${Number(pr.min_order_value || 0).toLocaleString('vi-VN')}₫)`)
    .join('\n');

  const catalogSummary =
    `Store & Brand Information:\n` +
    `- Brand: ROAR COFFEE® Vietnam — Specialty & Commercial Coffee Roaster + B2B Green Coffee Supplier.\n` +
    `- Operating Hours: ${openHoursVi}\n` +
    `- Hotline: ${hotline} | Zalo: ${zaloPhone} | Retail Email: ${contactEmail} | B2B Email: ${b2bEmail}\n` +
    `- Address: ${addressVi}\n` +
    `- Growing Regions (/regions): Cầu Đất (Đà Lạt, 1500m+ Arabica), Buôn Ma Thuột / Đắk Lắk (Fine Robusta), Gia Lai, Kon Tum, Lâm Đồng.\n` +
    `- Shipping Policy: Giao hàng toàn quốc 1–3 ngày (nội thành HCM 2–4h), miễn phí vận chuyển theo mốc đơn hàng cấu hình tại trang Thanh toán (/checkout).\n` +
    `- Order Tracking (/orders/track): Tra cứu bằng 1 trong 3 thông tin: Mã đơn hàng, Số điện thoại hoặc Email.\n` +
    `- B2B / HORECA / OEM (/partners, /coffee/green-beans): 27 mã Nhân xanh (Robusta/Arabica/Culi × S14/S16/S18 × Natural/Honey/CBU Washed), rang gia công OEM, mẫu thử COA.\n\n` +
    `Products:\n${catalogLines}\n\nActive Vouchers:\n${promoLines}`;

  try {
    const aiResult = await chatWithRoarBarista({
      message: cleanMsg,
      history: Array.isArray(history) ? history : [],
      lang: lang === 'en' ? 'en' : 'vi',
      catalogSummary,
    });

    const recommendedProducts = aiResult.recommendedSlugs
      .map((slug) => allProducts.find((p) => p.slug === slug))
      .filter(Boolean)
      .map(hydrateProductCard);

    res.json({
      ok: true,
      reply: aiResult.reply,
      recommendedProducts,
      quickLinks: aiResult.quickLinks,
    });
  } catch {
    const q = cleanMsg.toLowerCase();
    const isEn = lang === 'en';
    const kgMatch = q.match(/(\d+)\s*kg/);
    const requestedKg = kgMatch ? Math.max(1, Number(kgMatch[1])) : null;

    let matched: any[] = [];
    let quickLinks: Array<{ label: string; to: string }> = [];
    let reply = '';

    if (q.includes('giờ') || q.includes('mở cửa') || q.includes('làm việc') || q.includes('mấy giờ') || q.includes('hour') || q.includes('open') || q.includes('time')) {
      const nowStr = new Date().toLocaleTimeString(isEn ? 'en-US' : 'vi-VN', { hour: '2-digit', minute: '2-digit', timeZone: 'Asia/Ho_Chi_Minh' });
      reply = isEn
        ? `ROAR COFFEE® Operating Hours:\n• Office & Roastery: ${openHoursEn}\n• Current Vietnam time: ${nowStr}\n• Hotline: ${hotline} | Zalo: ${zaloPhone}`
        : `Giờ làm việc của ROAR COFFEE®:\n• Văn phòng & Xưởng rang: ${openHoursVi}\n• Giờ Việt Nam hiện tại: ${nowStr}\n• Hotline: ${hotline} | Zalo: ${zaloPhone}`;
      quickLinks = [{ label: isEn ? 'Contact Us' : 'Trang Liên hệ', to: '/contact' }];
    } else if (q.includes('địa chỉ') || q.includes('ở đâu') || q.includes('liên hệ') || q.includes('hotline') || q.includes('zalo') || q.includes('điện thoại') || q.includes('sđt') || q.includes('email') || q.includes('address') || q.includes('contact') || q.includes('phone')) {
      reply = isEn
        ? `ROAR COFFEE® Contact Information:\n• Hotline: ${hotline}\n• Zalo: ${zaloPhone}\n• Support Email: ${contactEmail}\n• B2B / Export Email: ${b2bEmail}\n• Address: ${addressEn}\n• Hours: ${openHoursEn}`
        : `Thông tin liên hệ ROAR COFFEE®:\n• Hotline: ${hotline}\n• Zalo: ${zaloPhone}\n• Email CSKH: ${contactEmail}\n• Email B2B / Xuất khẩu: ${b2bEmail}\n• Địa chỉ: ${addressVi}\n• Giờ làm việc: ${openHoursVi}`;
      quickLinks = [{ label: isEn ? 'Contact Page' : 'Xem trang Liên hệ', to: '/contact' }];
    } else if (q.includes('ship') || q.includes('vận chuyển') || q.includes('giao hàng') || q.includes('delivery') || q.includes('shipping')) {
      reply = isEn
        ? 'ROAR COFFEE® Shipping Policy:\n• Nationwide delivery in 1–3 business days (2–4h express in HCMC).\n• Shipping fees and free-shipping thresholds are automatically calculated at Checkout based on your order total.'
        : 'Chính sách giao hàng ROAR COFFEE®:\n• Giao hàng toàn quốc 1–3 ngày làm việc (nội thành TP.HCM giao nhanh 2–4 giờ).\n• Phí vận chuyển và mức Freeship được tính tự động theo tổng giá trị đơn hàng ngay tại bước Thanh toán.';
      quickLinks = [{ label: isEn ? 'Track Order' : 'Tra cứu đơn hàng', to: '/orders/track' }];
    } else if (q.includes('đơn hàng') || q.includes('tra cứu') || q.includes('kiểm tra đơn') || q.includes('track') || q.includes('order')) {
      reply = isEn
        ? 'You can track your ROAR COFFEE® order anytime using any of 3 options: Order Code, Phone Number, or Email address.'
        : 'Bạn có thể tra cứu trạng thái đơn hàng ROAR COFFEE® bất cứ lúc nào bằng 1 trong 3 thông tin: Mã đơn hàng, Số điện thoại hoặc Email đặt hàng.';
      quickLinks = [{ label: isEn ? 'Track Order Now' : 'Tra cứu đơn hàng ngay', to: '/orders/track' }];
    } else if (q.includes('voucher') || q.includes('mã giảm') || q.includes('khuyến mãi') || q.includes('ưu đãi') || q.includes('promo') || q.includes('discount')) {
      reply = isEn
        ? `Active ROAR COFFEE® Vouchers:\n${promoLines || 'Check our Promotions page for the latest offers!'}\nYou can pick or enter vouchers directly at Checkout.`
        : `Các mã Voucher ưu đãi đang áp dụng tại ROAR COFFEE®:\n${promoLines || 'Mời bạn xem trang Khuyến mãi để nhận ưu đãi mới nhất!'}\nBạn có thể chọn trực tiếp hoặc nhập mã ngay tại bước Thanh toán.`;
      quickLinks = [{ label: isEn ? 'View Promotions' : 'Xem tất cả Khuyến mãi', to: '/promotions' }];
    } else if (q.includes('vùng trồng') || q.includes('nguồn gốc') || q.includes('cầu đất') || q.includes('đắk lắk') || q.includes('tây nguyên') || q.includes('thương hiệu') || q.includes('giới thiệu') || q.includes('origin') || q.includes('story') || q.includes('about')) {
      reply = isEn
        ? 'ROAR COFFEE® sources directly from Vietnam’s finest highlands: Cầu Đất (Đà Lạt, 1,500m+ Arabica), Buôn Ma Thuột / Đắk Lắk (Fine Robusta), Gia Lai, and Kon Tum — roasted fresh to express 7 distinct Brand Personalities.'
        : 'ROAR COFFEE® tuyển chọn trực tiếp từ các vùng nguyên liệu trứ danh Việt Nam: Cầu Đất (Đà Lạt 1.500m+ cho Arabica), Buôn Ma Thuột / Đắk Lắk (Fine Robusta), Gia Lai & Kon Tum — rang mới mỗi mẻ theo 7 Cá tính thương hiệu riêng biệt.';
      quickLinks = [
        { label: isEn ? 'Growing Regions' : 'Khám phá Vùng trồng', to: '/regions' },
        { label: isEn ? 'Brand Story' : 'Câu chuyện ROAR', to: '/about' },
      ];
    } else if (q.includes('cách pha') || q.includes('pha chế') || q.includes('nhiệt độ') || q.includes('tỉ lệ') || q.includes('brew') || q.includes('recipe')) {
      reply = isEn
        ? 'ROAR Brewing Tips:\n• Vietnamese Phin: 25g coffee + 25ml bloom (30s) + 65ml water at 92–95°C.\n• Espresso: 18g in → 36g out in 27–30s at 93°C.\n• Pour Over (V60): 15g coffee + 240ml water at 91–93°C (2m30s).'
        : 'Gợi ý pha chế chuẩn vị ROAR COFFEE®:\n• Pha Phin: 25g cà phê, ủ 25ml nước (30s), rót thêm 65ml nước 92–95°C.\n• Pha Espresso: 18g bột → chiết xuất 36g trong 27–30 giây ở 93°C.\n• Pour Over (V60): 15g cà phê + 240ml nước 91–93°C (khoảng 2 phút 30 giây).';
      quickLinks = [{ label: isEn ? 'Full Brewing Guide' : 'Xem Cẩm nang pha chế', to: '/brewing' }];
    } else if (q.includes('b2b') || q.includes('nhân xanh') || q.includes('đại lý') || q.includes('oem') || q.includes('xuất khẩu') || q.includes('hợp tác') || q.includes('partner') || q.includes('export')) {
      reply = isEn
        ? `ROAR COFFEE® B2B & Export:\n• 27 Green Coffee SKUs (Robusta/Arabica/Culi × S14/S16/S18 × Natural/Honey/CBU Washed) with COA.\n• Private-label OEM roasting & HORECA wholesale supply.\n• Direct B2B contact: ${b2bEmail} | Hotline/Zalo: ${hotline}`
        : `Hợp tác B2B, Đại lý & Xuất khẩu ROAR COFFEE®:\n• 27 mã Cà phê Nhân xanh chuẩn xuất khẩu (Robusta/Arabica/Culi × S14/S16/S18 × Natural/Honey/CBU Washed) đầy đủ COA.\n• Nhận rang gia công OEM & cung ứng sỉ cho chuỗi quán HORECA.\n• Liên hệ B2B: ${b2bEmail} | Hotline/Zalo: ${hotline}`;
      quickLinks = [
        { label: isEn ? '27 Green Coffee SKUs' : '27 mã Nhân xanh B2B', to: '/coffee/green-beans' },
        { label: isEn ? 'B2B Partnership' : 'Đăng ký Đối tác B2B', to: '/partners' },
      ];
    } else if (q.includes('kg') || q.includes('sỉ') || q.includes('hạt rang') || q.includes('s18') || q.includes('báo giá') || q.includes('wholesale')) {
      const beans = allProducts.filter((p) => p.category === 'roasted_beans');
      matched = beans.filter((p) => {
        if (q.includes('arabica')) return p.name_vi.toLowerCase().includes('arabica');
        if (q.includes('culi')) return p.name_vi.toLowerCase().includes('culi');
        if (q.includes('honey')) return p.name_vi.toLowerCase().includes('honey');
        if (q.includes('cbu')) return p.name_vi.toLowerCase().includes('cbu');
        if (q.includes('robusta')) return p.name_vi.toLowerCase().includes('robusta');
        return true;
      });
      if (matched.length === 0) matched = beans;
      const top = matched.slice(0, 3);
      if (requestedKg) {
        const quoteLines = top
          .map((p) => {
            const tiers = JSON.parse(p.pricing_tiers_json || '[]');
            const tier = resolveVolumeTier(tiers, requestedKg);
            const unitP = tier ? tier.priceVnd : p.price_vnd;
            return `• ${p.name_vi} (${p.sub_category}): ${unitP.toLocaleString('vi-VN')} ₫/kg → ${requestedKg} kg = ${(unitP * requestedKg).toLocaleString('vi-VN')} ₫`;
          })
          .join('\n');
        reply = isEn
          ? `Here is your instant quote for ${requestedKg} kg of ROAR Roasted Coffee Beans:\n${quoteLines}`
          : `Báo giá nhanh cho ${requestedKg} kg Cà phê Hạt rang ROAR (tự động áp dụng mức giá theo số kg):\n${quoteLines}`;
      } else {
        reply = isEn
          ? 'ROAR Roasted Coffee Beans include 6 S18 SKUs with automatic 5-tier kg pricing (1kg, 5–19kg, 20–49kg, 50–99kg, Wholesale ≥100kg from 180,000 VND/kg). Select a product below to enter your exact kg:'
          : 'Danh mục Cà phê Hạt rang ROAR gồm 6 mã S18 có bảng giá tự động 5 mức theo kg (1kg, 5–19kg, 20–49kg, 50–99kg, Sỉ ≥100kg từ 180.000 ₫/kg). Bạn bấm chọn sản phẩm bên dưới để nhập số kg nhé:';
      }
      quickLinks = [{ label: isEn ? 'View All Roasted Beans (kg)' : 'Xem bảng giá Cà phê Hạt rang (kg)', to: '/coffee/roasted-beans' }];
    } else if (q.includes('phin') || q.includes('đậm') || q.includes('mạnh') || q.includes('sữa đá') || q.includes('robusta')) {
      matched = allProducts.filter((p) => p.slug.includes('lion') || p.slug.includes('tiger') || p.slug.includes('robusta')).slice(0, 3);
      reply = isEn
        ? 'For a bold, rich Vietnamese Phin or iced milk coffee, I recommend Lion (Sư Tử — Traditional Phin), Tiger (Hổ — Bold Robusta), or Robusta S18. Click any product below to view details or add to cart:'
        : 'Với gu đậm đà, pha Phin truyền thống hoặc cà phê sữa đá, mình gợi ý Sư Tử (Lion), Hổ (Tiger) hoặc Robusta S18. Bạn bấm trực tiếp vào sản phẩm bên dưới để xem chi tiết & chọn mua nhé:';
      quickLinks = [{ label: isEn ? 'Brewing Guide' : 'Hướng dẫn pha Phin chuẩn', to: '/brewing' }];
    } else if (q.includes('espresso') || q.includes('arabica') || q.includes('chua thanh') || q.includes('nhẹ') || q.includes('quà') || q.includes('signature')) {
      matched = allProducts
        .filter((p) => p.slug.includes('signature') || p.slug.includes('fox') || p.slug.includes('eagle') || p.slug.includes('arabica'))
        .slice(0, 3);
      reply = isEn
        ? 'For smooth Espresso, aromatic Arabica, or luxury gifting, explore Black Panther Signature Reserve, Fox Espresso, or Arabica S18 CBU below:'
        : 'Với gu Espresso hậu ngọt, hương thơm tinh tế hoặc làm quà biếu cao cấp, bạn hãy chọn Báo Đen Signature Reserve, Cáo Espresso hoặc Arabica S18 CBU bên dưới nhé:';
      quickLinks = [{ label: isEn ? 'Explore 7 Personalities' : 'Khám phá 7 Cá tính ROAR', to: '/personalities' }];
    } else {
      matched = allProducts.filter((p) => p.category === 'roasted' || p.category === 'roasted_beans').slice(0, 3);
      reply = isEn
        ? 'Hello from ROAR COFFEE®! You can ask me anything: coffee taste recommendations, 5-tier kg quotes, operating hours, contact/Zalo, shipping, vouchers, brewing guides, or B2B green coffee!'
        : 'Xin chào từ ROAR COFFEE®! Bạn có thể hỏi mình bất cứ thông tin nào: chọn cà phê theo gu, báo giá hạt rang theo kg, giờ làm việc, địa chỉ/Zalo, phí vận chuyển, voucher, cách pha chế hay hợp tác B2B nhé!';
      quickLinks = [
        { label: isEn ? 'Roasted Beans (5-tier kg)' : 'Cà phê Hạt rang (5 mức kg)', to: '/coffee/roasted-beans' },
        { label: isEn ? 'Vouchers & Promos' : 'Xem Voucher ưu đãi', to: '/promotions' },
      ];
    }

    res.json({
      ok: true,
      reply,
      recommendedProducts: matched.slice(0, 3).map(hydrateProductCard),
      quickLinks,
      fallback: true,
    });
  }
});

app.post('/api/auth/logout', (req, res) => {
  const https = isHttpsRequest(req);
  res.clearCookie(SESSION_COOKIE_NAME, {
    path: '/',
    sameSite: https ? 'none' : 'lax',
    secure: https,
  });
  res.json({ ok: true });
});

app.post('/api/auth/verify-email', requireAuth, (req: AuthedRequest, res) => {
  db.prepare('UPDATE users SET email_verified = 1, verification_token = NULL WHERE id = ?').run(req.authUser!.userId);
  res.json({ ok: true, emailVerified: true });
});

app.post('/api/auth/forgot-password', (req, res) => {
  const { email } = req.body || {};
  if (!email) {
    res.status(400).json({ error: 'Email is required' });
    return;
  }
  const normalizedEmail = String(email).trim().toLowerCase();
  const user = db.prepare('SELECT id FROM users WHERE email = ?').get(normalizedEmail) as { id: number } | undefined;
  if (!user) {
    res.json({ ok: true, message: 'If an account matches this email, recovery instructions have been issued.' });
    return;
  }
  const resetToken = crypto.randomBytes(6).toString('hex').toUpperCase();
  const resetExpires = Math.floor(Date.now() / 1000) + 1800;
  db.prepare('UPDATE users SET reset_token = ?, reset_expires = ? WHERE id = ?').run(resetToken, resetExpires, user.id);
  res.json({
    ok: true,
    demoResetCode: resetToken,
    message: 'Password recovery token issued (displayed in development mode because SMTP is not connected).',
  });
});

app.post('/api/auth/reset-password', (req, res) => {
  const { email, token, newPassword } = req.body || {};
  if (!email || !token || !newPassword || String(newPassword).length < 8) {
    res.status(400).json({ error: 'Valid email, recovery code, and new password (min 8 chars) required' });
    return;
  }
  const user = db.prepare('SELECT id, reset_token, reset_expires FROM users WHERE email = ?').get(String(email).trim().toLowerCase()) as any;
  if (!user || user.reset_token !== String(token).trim().toUpperCase() || !user.reset_expires || user.reset_expires < Math.floor(Date.now() / 1000)) {
    res.status(400).json({ error: 'Invalid or expired recovery code' });
    return;
  }
  db.prepare('UPDATE users SET password_hash = ?, reset_token = NULL, reset_expires = NULL WHERE id = ?').run(
    hashPassword(String(newPassword)),
    user.id
  );
  res.json({ ok: true });
});

app.get('/api/auth/me', (req: AuthedRequest, res) => {
  if (!req.authUser) {
    res.json({ user: null });
    return;
  }
  const user = db.prepare('SELECT * FROM users WHERE id = ?').get(req.authUser.userId) as any;
  if (!user) {
    res.json({ user: null });
    return;
  }
  const syncedTier = syncUserTierInDb(user.id);
  const points = getPointsSummary(user.id);
  const unreadNotifications = (
    db.prepare('SELECT COUNT(*) as c FROM user_notifications WHERE user_id = ? AND is_read = 0').get(user.id) as { c: number }
  ).c;
  const rbac = resolveEffectiveAdminPermissions(user);
  res.json({
    user: {
      id: user.id,
      email: user.email,
      fullName: user.full_name,
      phone: user.phone,
      role: user.role,
      adminRole: rbac.adminRole,
      adminPermissions: rbac.adminPermissions,
      memberCode: user.member_code,
      tier: syncedTier,
      emailVerified: Boolean(user.email_verified),
      addresses: JSON.parse(user.addresses_json || '[]'),
      notificationPrefs: JSON.parse(user.notification_prefs_json || '{}'),
      privacyPrefs: JSON.parse(user.privacy_prefs_json || '{}'),
      deletionRequested: Boolean(user.deletion_requested),
      companyName: user.company_name,
      b2bVerified: Boolean(user.b2b_verified),
      points,
      walletBalanceVnd: Number(user.wallet_balance_vnd || 0),
      unreadNotifications,
    },
  });
});

const WALLET_TOPUP_PACKAGES = [
  { amountVnd: 100000, bonusPct: 10, labelVi: 'Gói Khởi Động · Tặng +10%', labelEn: 'Starter Pack · +10% Bonus' },
  { amountVnd: 500000, bonusPct: 15, labelVi: 'Gói Thành Viên · Tặng +15%', labelEn: 'Member Pack · +15% Bonus' },
  { amountVnd: 1000000, bonusPct: 20, labelVi: 'Gói Vàng (Gold) · Tặng +20%', labelEn: 'Gold Pack · +20% Bonus' },
  { amountVnd: 2000000, bonusPct: 30, labelVi: 'Gói Reserve VIP · Tặng +30%', labelEn: 'Reserve VIP · +30% Bonus' },
];

function resolveWalletBonusPct(amountVnd: number): number {
  if (amountVnd >= 2000000) return 30;
  if (amountVnd >= 1000000) return 20;
  if (amountVnd >= 500000) return 15;
  return 10;
}

app.get('/api/wallet', requireAuth, (req: AuthedRequest, res) => {
  const user = db.prepare('SELECT id, full_name, member_code, tier, wallet_balance_vnd FROM users WHERE id = ?').get(req.authUser!.userId) as any;
  if (!user) {
    res.status(404).json({ error: 'User not found' });
    return;
  }
  const syncedTier = syncUserTierInDb(user.id);
  const points = getPointsSummary(user.id);
  const transactions = db
    .prepare('SELECT * FROM wallet_transactions WHERE user_id = ? ORDER BY id DESC LIMIT 30')
    .all(user.id);
  res.json({
    walletBalanceVnd: Number(user.wallet_balance_vnd || 0),
    points,
    tier: syncedTier,
    memberCode: user.member_code,
    packages: WALLET_TOPUP_PACKAGES.map((p) => {
      const bonusVnd = Math.round((p.amountVnd * p.bonusPct) / 100);
      return {
        ...p,
        bonusVnd,
        totalCreditVnd: p.amountVnd + bonusVnd,
        bonusPoints: Math.floor((p.amountVnd + bonusVnd) / 10000),
      };
    }),
    transactions,
  });
});

function getWalletApprovalMode(): 'manual' | 'auto' {
  const row = db.prepare(`SELECT value FROM site_settings WHERE key = 'wallet_approval_mode'`).get() as any;
  return row?.value === 'auto' ? 'auto' : 'manual';
}

app.post('/api/wallet/topup', requireAuth, (req: AuthedRequest, res) => {
  const amountVnd = Math.floor(Number(req.body?.amountVnd || 0));
  if (!Number.isFinite(amountVnd) || amountVnd < 50000) {
    res.status(400).json({ error: 'Số tiền nạp tối thiểu là 50.000₫' });
    return;
  }
  const bonusPct = resolveWalletBonusPct(amountVnd);
  const bonusVnd = Math.round((amountVnd * bonusPct) / 100);
  const totalCreditVnd = amountVnd + bonusVnd;
  const pointsDelta = Math.floor(totalCreditVnd / 10000);
  const refCode = String(req.body?.referenceCode || `TOPUP-${Date.now().toString(36).toUpperCase()}`);
  const approvalMode = getWalletApprovalMode();

  if (approvalMode === 'manual') {
    const ins = db
      .prepare(`
        INSERT INTO wallet_topup_requests (user_id, amount_vnd, bonus_pct, bonus_vnd, total_credit_vnd, points_delta, reference_code, status)
        VALUES (?, ?, ?, ?, ?, ?, ?, 'pending')
      `)
      .run(req.authUser!.userId, amountVnd, bonusPct, bonusVnd, totalCreditVnd, pointsDelta, refCode);

    // Notify member that top-up request is pending company bank verification
    createUserNotification(req.authUser!.userId, {
      category: 'loyalty',
      titleVi: `Đã tiếp nhận yêu cầu nạp Ví ROAR (${refCode})`,
      titleEn: `ROAR Wallet top-up request received (${refCode})`,
      messageVi: `Yêu cầu nạp ${amountVnd.toLocaleString('vi-VN')}₫ (+${bonusPct}% thưởng = ${totalCreditVnd.toLocaleString('vi-VN')}₫) đang chờ kế toán ROAR xác nhận chuyển khoản.`,
      messageEn: `Your ${amountVnd.toLocaleString('en-US')} VND top-up request (+${bonusPct}% bonus) is pending bank transfer verification.`,
      linkUrl: '/account?tab=wallet',
    });

    const currentUserRow = db.prepare('SELECT wallet_balance_vnd FROM users WHERE id = ?').get(req.authUser!.userId) as any;
    res.json({
      ok: true,
      status: 'pending',
      approvalMode: 'manual',
      requestId: Number(ins.lastInsertRowid),
      referenceCode: refCode,
      amountVnd,
      bonusPct,
      bonusVnd,
      totalCreditVnd,
      pointsDelta,
      walletBalanceVnd: Number(currentUserRow?.wallet_balance_vnd || 0),
    });
    return;
  }

  // Auto approval mode (transactional)
  db.transaction(() => {
    db.prepare(`
      INSERT INTO wallet_topup_requests (user_id, amount_vnd, bonus_pct, bonus_vnd, total_credit_vnd, points_delta, reference_code, status, reviewed_at, admin_note)
      VALUES (?, ?, ?, ?, ?, ?, ?, 'approved', datetime('now'), 'Tự động duyệt')
    `).run(req.authUser!.userId, amountVnd, bonusPct, bonusVnd, totalCreditVnd, pointsDelta, refCode);

    db.prepare('UPDATE users SET wallet_balance_vnd = wallet_balance_vnd + ? WHERE id = ?').run(
      totalCreditVnd,
      req.authUser!.userId
    );

    db.prepare(`
      INSERT INTO wallet_transactions (user_id, tx_type, amount_vnd, bonus_vnd, bonus_pct, points_delta, note, reference_code)
      VALUES (?, 'topup', ?, ?, ?, ?, ?, ?)
    `).run(
      req.authUser!.userId,
      amountVnd,
      bonusVnd,
      bonusPct,
      pointsDelta,
      `Nạp ví ${amountVnd.toLocaleString('vi-VN')}₫ + Thưởng ${bonusPct}% (${bonusVnd.toLocaleString('vi-VN')}₫)`,
      refCode
    );

    if (pointsDelta > 0) {
      db.prepare(`
        INSERT INTO points_ledger (user_id, order_id, entry_type, points, description_vi, description_en, expires_at)
        VALUES (?, NULL, 'earn_available', ?, ?, ?, datetime('now', '+365 days'))
      `).run(
        req.authUser!.userId,
        pointsDelta,
        `Tích điểm thưởng khi nạp Ví ROAR (${refCode})`,
        `Reward points earned from ROAR Wallet top-up (${refCode})`
      );
    }

    createUserNotification(req.authUser!.userId, {
      category: 'loyalty',
      titleVi: `Nạp Ví ROAR thành công +${totalCreditVnd.toLocaleString('vi-VN')}₫`,
      titleEn: `ROAR Wallet top-up approved +${totalCreditVnd.toLocaleString('en-US')} VND`,
      messageVi: `Tài khoản công ty đã ghi nhận khoản nạp ${amountVnd.toLocaleString('vi-VN')}₫ (+${bonusPct}% thưởng) và cộng +${pointsDelta} điểm thưởng.`,
      messageEn: `Your top-up of ${amountVnd.toLocaleString('en-US')} VND (+${bonusPct}% bonus) has been credited with +${pointsDelta} pts.`,
      linkUrl: '/account?tab=wallet',
    });
  })();

  syncUserTierInDb(req.authUser!.userId);
  const updatedUser = db.prepare('SELECT wallet_balance_vnd FROM users WHERE id = ?').get(req.authUser!.userId) as any;
  res.json({
    ok: true,
    status: 'approved',
    approvalMode: 'auto',
    referenceCode: refCode,
    amountVnd,
    bonusPct,
    bonusVnd,
    totalCreditVnd,
    pointsDelta,
    walletBalanceVnd: Number(updatedUser?.wallet_balance_vnd || 0),
  });
});

app.get('/api/admin/wallet/requests', requirePermission('customers', 'promotions', 'orders'), (_req, res) => {
  const requests = db
    .prepare(`
      SELECT r.*, u.full_name, u.email, u.member_code
      FROM wallet_topup_requests r
      LEFT JOIN users u ON u.id = r.user_id
      ORDER BY CASE WHEN r.status = 'pending' THEN 0 ELSE 1 END, r.id DESC
      LIMIT 100
    `)
    .all();
  res.json({
    approvalMode: getWalletApprovalMode(),
    requests,
  });
});

app.patch('/api/admin/wallet/approval-mode', requirePermission('customers', 'promotions', 'orders'), (req: AuthedRequest, res) => {
  const mode = req.body?.mode === 'auto' ? 'auto' : 'manual';
  db.prepare(
    `INSERT INTO site_settings (key, value) VALUES ('wallet_approval_mode', ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value`
  ).run(mode);
  res.json({ ok: true, approvalMode: mode });
});

app.post('/api/admin/wallet/requests/:id/approve', requirePermission('customers', 'promotions', 'orders'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const row = db.prepare('SELECT * FROM wallet_topup_requests WHERE id = ?').get(id) as any;
  if (!row) {
    res.status(404).json({ error: 'Không tìm thấy yêu cầu nạp tiền.' });
    return;
  }
  if (row.status !== 'pending') {
    res.status(400).json({ error: 'Yêu cầu này đã được xử lý trước đó.' });
    return;
  }
  const adminNote = String(req.body?.adminNote || 'Công ty đã xác nhận nhận tiền chuyển khoản').trim();

  db.transaction(() => {
    const updatedReq = db.prepare(
      `UPDATE wallet_topup_requests SET status = 'approved', admin_note = ?, reviewed_by = ?, reviewed_at = datetime('now') WHERE id = ? AND status = 'pending'`
    ).run(adminNote, req.authUser!.userId, id);
    if (updatedReq.changes === 0) return;

    db.prepare('UPDATE users SET wallet_balance_vnd = wallet_balance_vnd + ? WHERE id = ?').run(
      Number(row.total_credit_vnd),
      row.user_id
    );

    db.prepare(`
      INSERT INTO wallet_transactions (user_id, tx_type, amount_vnd, bonus_vnd, bonus_pct, points_delta, note, reference_code)
      VALUES (?, 'topup', ?, ?, ?, ?, ?, ?)
    `).run(
      row.user_id,
      row.amount_vnd,
      row.bonus_vnd,
      row.bonus_pct,
      row.points_delta,
      `Duyệt nạp ví ${Number(row.amount_vnd).toLocaleString('vi-VN')}₫ + Thưởng ${row.bonus_pct}% (${adminNote})`,
      row.reference_code
    );

    if (Number(row.points_delta) > 0) {
      db.prepare(`
        INSERT INTO points_ledger (user_id, order_id, entry_type, points, description_vi, description_en, expires_at)
        VALUES (?, NULL, 'earn_available', ?, ?, ?, datetime('now', '+365 days'))
      `).run(
        row.user_id,
        row.points_delta,
        `Tích điểm thưởng khi duyệt nạp Ví ROAR (${row.reference_code})`,
        `Reward points earned from approved ROAR Wallet top-up (${row.reference_code})`
      );
    }

    createUserNotification(row.user_id, {
      category: 'loyalty',
      titleVi: `Công ty đã nhận tiền! Nạp Ví ROAR thành công +${Number(row.total_credit_vnd).toLocaleString('vi-VN')}₫`,
      titleEn: `Bank transfer confirmed! +${Number(row.total_credit_vnd).toLocaleString('en-US')} VND credited`,
      messageVi: `ROAR COFFEE đã xác nhận nhận chuyển khoản ${Number(row.amount_vnd).toLocaleString('vi-VN')}₫ (Mã ${row.reference_code}). Ví ROAR đã được cộng ${Number(row.total_credit_vnd).toLocaleString('vi-VN')}₫ (+${row.bonus_pct}% thưởng) và +${row.points_delta} điểm.`,
      messageEn: `ROAR COFFEE confirmed your bank transfer (${row.reference_code}). Credited ${Number(row.total_credit_vnd).toLocaleString('en-US')} VND and +${row.points_delta} pts.`,
      linkUrl: '/account?tab=wallet',
    });

    logAudit(req.authUser!.userId, req.authUser!.email, 'APPROVE_WALLET_TOPUP', 'wallet_topup_requests', id, {
      userId: row.user_id,
      amountVnd: row.amount_vnd,
      totalCreditVnd: row.total_credit_vnd,
      referenceCode: row.reference_code,
    });
  })();

  syncUserTierInDb(row.user_id);
  res.json({ ok: true });
});

app.post('/api/admin/wallet/requests/:id/reject', requirePermission('customers', 'promotions', 'orders'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const row = db.prepare('SELECT * FROM wallet_topup_requests WHERE id = ?').get(id) as any;
  if (!row) {
    res.status(404).json({ error: 'Không tìm thấy yêu cầu nạp tiền.' });
    return;
  }
  if (row.status !== 'pending') {
    res.status(400).json({ error: 'Yêu cầu này đã được xử lý trước đó.' });
    return;
  }
  const adminNote = String(req.body?.adminNote || 'Chưa nhận được chuyển khoản hợp lệ').trim();

  db.transaction(() => {
    db.prepare(
      `UPDATE wallet_topup_requests SET status = 'rejected', admin_note = ?, reviewed_by = ?, reviewed_at = datetime('now') WHERE id = ? AND status = 'pending'`
    ).run(adminNote, req.authUser!.userId, id);

    createUserNotification(row.user_id, {
      category: 'loyalty',
      titleVi: `Yêu cầu nạp Ví ROAR chưa được duyệt (${row.reference_code})`,
      titleEn: `ROAR Wallet top-up request declined (${row.reference_code})`,
      messageVi: `Yêu cầu nạp ${Number(row.amount_vnd).toLocaleString('vi-VN')}₫ chưa được duyệt. Lý do: ${adminNote}. Vui lòng liên hệ Hotline/Zalo ROAR để được hỗ trợ.`,
      messageEn: `Your top-up request (${row.reference_code}) was declined. Reason: ${adminNote}.`,
      linkUrl: '/account?tab=wallet',
    });

    logAudit(req.authUser!.userId, req.authUser!.email, 'REJECT_WALLET_TOPUP', 'wallet_topup_requests', id, {
      userId: row.user_id,
      referenceCode: row.reference_code,
      adminNote,
    });
  })();

  res.json({ ok: true });
});

const CHECKIN_REWARD_SCHEDULE = [
  { day: 1, points: 10, bonusVi: '', bonusEn: '' },
  { day: 2, points: 15, bonusVi: '', bonusEn: '' },
  { day: 3, points: 40, bonusVi: 'Bonus chuỗi 3 ngày liên tục!', bonusEn: '3-Day Streak Bonus!' },
  { day: 4, points: 20, bonusVi: '', bonusEn: '' },
  { day: 5, points: 25, bonusVi: '', bonusEn: '' },
  { day: 6, points: 30, bonusVi: '', bonusEn: '' },
  { day: 7, points: 100, bonusVi: 'Quà VIP 7 ngày: +100 điểm & Voucher ROAR7DAY (-15%)', bonusEn: '7-Day VIP Gift: +100 pts & Voucher ROAR7DAY (15% OFF)' },
];

function getVietnamDateStr(offsetDays = 0): string {
  const now = new Date(Date.now() + offsetDays * 86400000);
  return new Intl.DateTimeFormat('en-CA', { timeZone: 'Asia/Ho_Chi_Minh' }).format(now);
}

app.get('/api/checkin/status', requireAuth, (req: AuthedRequest, res) => {
  const userId = req.authUser!.userId;
  const today = getVietnamDateStr(0);
  const yesterday = getVietnamDateStr(-1);
  const rows = db
    .prepare('SELECT checkin_date, streak_day, points_awarded, bonus_reward FROM daily_checkins WHERE user_id = ? ORDER BY checkin_date DESC LIMIT 14')
    .all(userId) as any[];

  const latest = rows[0];
  const checkedInToday = latest?.checkin_date === today;
  let currentStreak = 0;
  if (latest?.checkin_date === today || latest?.checkin_date === yesterday) {
    currentStreak = Number(latest.streak_day || 0);
  }
  const totalCheckins = (db.prepare('SELECT COUNT(*) as c FROM daily_checkins WHERE user_id = ?').get(userId) as { c: number }).c;
  const nextCycleDay = (currentStreak % 7) + 1;

  res.json({
    today,
    checkedInToday,
    currentStreak,
    nextCycleDay,
    totalCheckins,
    schedule: CHECKIN_REWARD_SCHEDULE,
    history: rows,
  });
});

app.post('/api/checkin', requireAuth, (req: AuthedRequest, res) => {
  const userId = req.authUser!.userId;
  const today = getVietnamDateStr(0);
  const yesterday = getVietnamDateStr(-1);

  const existing = db.prepare('SELECT id FROM daily_checkins WHERE user_id = ? AND checkin_date = ?').get(userId, today);
  if (existing) {
    res.status(400).json({ error: 'Bạn đã điểm danh hôm nay rồi! Hẹn gặp bạn vào ngày mai nhé.' });
    return;
  }

  const prev = db.prepare('SELECT streak_day FROM daily_checkins WHERE user_id = ? AND checkin_date = ?').get(userId, yesterday) as any;
  const newStreak = prev ? Number(prev.streak_day || 0) + 1 : 1;
  const cycleDay = ((newStreak - 1) % 7) + 1;
  const rule = CHECKIN_REWARD_SCHEDULE[cycleDay - 1] || CHECKIN_REWARD_SCHEDULE[0];

  db.prepare(`
    INSERT INTO daily_checkins (user_id, checkin_date, streak_day, points_awarded, bonus_reward)
    VALUES (?, ?, ?, ?, ?)
  `).run(userId, today, newStreak, rule.points, rule.bonusVi);

  db.prepare(`
    INSERT INTO points_ledger (user_id, order_id, entry_type, points, description_vi, description_en, expires_at)
    VALUES (?, NULL, 'earn_available', ?, ?, ?, datetime('now', '+365 days'))
  `).run(
    userId,
    rule.points,
    `Điểm danh ngày ${newStreak}${rule.bonusVi ? ` · ${rule.bonusVi}` : ''}`,
    `Daily Check-in Day ${newStreak}${rule.bonusEn ? ` · ${rule.bonusEn}` : ''}`
  );

  syncUserTierInDb(userId);
  res.json({
    ok: true,
    checkinDate: today,
    streakDay: newStreak,
    cycleDay,
    pointsAwarded: rule.points,
    bonusVi: rule.bonusVi,
    bonusEn: rule.bonusEn,
    points: getPointsSummary(userId),
  });
});

app.get('/api/admin/wallets', requirePermission('customers', 'promotions', 'orders'), (_req, res) => {
  const members = db
    .prepare(
      `SELECT id, full_name, email, phone, member_code, tier, role, wallet_balance_vnd, created_at
       FROM users ORDER BY wallet_balance_vnd DESC, id DESC LIMIT 100`
    )
    .all() as any[];

  const enriched = members.map((m) => ({
    ...m,
    tier: syncUserTierInDb(m.id),
    points: getPointsSummary(m.id),
  }));

  const transactions = db
    .prepare(
      `SELECT wt.*, u.full_name, u.email, u.member_code
       FROM wallet_transactions wt
       JOIN users u ON u.id = wt.user_id
       ORDER BY wt.id DESC LIMIT 60`
    )
    .all();

  res.json({ members: enriched, transactions });
});

app.post('/api/admin/wallets/adjust', requirePermission('customers', 'promotions', 'orders'), (req: AuthedRequest, res) => {
  const userId = Number(req.body?.userId || 0);
  const amountVnd = Math.floor(Number(req.body?.amountVnd || 0));
  const pointsDelta = Math.floor(Number(req.body?.pointsDelta || 0));
  const applyBonus = Boolean(req.body?.applyBonus);
  const note = String(req.body?.note || '').trim();

  const target = db.prepare('SELECT id, email, full_name, wallet_balance_vnd FROM users WHERE id = ?').get(userId) as any;
  if (!target) {
    res.status(404).json({ error: 'Không tìm thấy thành viên.' });
    return;
  }

  let bonusPct = 0;
  let bonusVnd = 0;
  let totalCreditVnd = amountVnd;
  let autoPoints = 0;

  if (amountVnd > 0 && applyBonus) {
    bonusPct = resolveWalletBonusPct(amountVnd);
    bonusVnd = Math.round((amountVnd * bonusPct) / 100);
    totalCreditVnd = amountVnd + bonusVnd;
    autoPoints = Math.floor(totalCreditVnd / 10000);
  }

  const finalPoints = pointsDelta + autoPoints;
  const refCode = `ADM-${Date.now().toString(36).toUpperCase()}`;

  if (totalCreditVnd !== 0) {
    db.prepare('UPDATE users SET wallet_balance_vnd = MAX(0, wallet_balance_vnd + ?) WHERE id = ?').run(
      totalCreditVnd,
      userId
    );
    db.prepare(`
      INSERT INTO wallet_transactions (user_id, tx_type, amount_vnd, bonus_vnd, bonus_pct, points_delta, note, reference_code)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?)
    `).run(
      userId,
      totalCreditVnd > 0 ? 'topup' : 'spend',
      amountVnd,
      bonusVnd,
      bonusPct,
      finalPoints,
      note || (totalCreditVnd > 0 ? `Admin nạp ví +${totalCreditVnd.toLocaleString('vi-VN')}₫` : `Admin điều chỉnh ví ${totalCreditVnd.toLocaleString('vi-VN')}₫`),
      refCode
    );
  }

  if (finalPoints !== 0) {
    db.prepare(`
      INSERT INTO points_ledger (user_id, order_id, entry_type, points, description_vi, description_en, expires_at)
      VALUES (?, NULL, ?, ?, ?, ?, datetime('now', '+365 days'))
    `).run(
      userId,
      finalPoints > 0 ? 'earn_available' : 'redeem',
      finalPoints,
      note || `Admin điều chỉnh điểm (${refCode})`,
      note || `Admin points adjustment (${refCode})`
    );
  }

  logAudit(req.authUser!.userId, req.authUser!.email, 'wallet_adjust', 'user', userId, {
    amountVnd,
    bonusPct,
    bonusVnd,
    finalPoints,
    note,
  });

  syncUserTierInDb(userId);
  const updated = db.prepare('SELECT wallet_balance_vnd FROM users WHERE id = ?').get(userId) as any;
  res.json({
    ok: true,
    walletBalanceVnd: Number(updated?.wallet_balance_vnd || 0),
    points: getPointsSummary(userId),
    referenceCode: refCode,
  });
});

// ---------- MEMBER PROFILE & ACCOUNT ----------
app.patch('/api/account/profile', requireAuth, (req: AuthedRequest, res) => {
  const { fullName, phone, addresses, notificationPrefs, privacyPrefs } = req.body || {};
  const userId = req.authUser!.userId;
  const current = db.prepare('SELECT * FROM users WHERE id = ?').get(userId) as any;
  if (!current) {
    res.status(404).json({ error: 'Account not found' });
    return;
  }
  db.prepare(`
    UPDATE users SET full_name = ?, phone = ?, addresses_json = ?, notification_prefs_json = ?, privacy_prefs_json = ?
    WHERE id = ?
  `).run(
    fullName ? String(fullName).trim() : current.full_name,
    phone !== undefined ? String(phone).trim() : current.phone,
    addresses ? JSON.stringify(addresses) : current.addresses_json,
    notificationPrefs ? JSON.stringify(notificationPrefs) : current.notification_prefs_json,
    privacyPrefs ? JSON.stringify(privacyPrefs) : current.privacy_prefs_json,
    userId
  );
  res.json({ ok: true });
});

app.post('/api/account/change-password', requireAuth, (req: AuthedRequest, res) => {
  const { currentPassword, newPassword } = req.body || {};
  if (!currentPassword || !newPassword || String(newPassword).length < 8) {
    res.status(400).json({ error: 'Current password and new password (min 8 chars) required' });
    return;
  }
  const user = db.prepare('SELECT password_hash FROM users WHERE id = ?').get(req.authUser!.userId) as any;
  if (!user || !verifyPassword(String(currentPassword), user.password_hash)) {
    res.status(401).json({ error: 'Current password is incorrect' });
    return;
  }
  db.prepare('UPDATE users SET password_hash = ? WHERE id = ?').run(hashPassword(String(newPassword)), req.authUser!.userId);
  res.json({ ok: true });
});

app.post('/api/account/request-deletion', requireAuth, (req: AuthedRequest, res) => {
  db.prepare('UPDATE users SET deletion_requested = 1 WHERE id = ?').run(req.authUser!.userId);
  res.json({ ok: true });
});

app.get('/api/account/dashboard', requireAuth, (req: AuthedRequest, res) => {
  const userId = req.authUser!.userId;
  const syncedTier = syncUserTierInDb(userId);
  const user = db.prepare('SELECT id, email, full_name, phone, role, member_code, tier, email_verified, addresses_json, notification_prefs_json, privacy_prefs_json, deletion_requested FROM users WHERE id = ?').get(userId) as any;
  const points = getPointsSummary(userId);
  const ledger = db
    .prepare('SELECT * FROM points_ledger WHERE user_id = ? ORDER BY created_at DESC, id DESC LIMIT 50')
    .all(userId);
  const orders = db
    .prepare('SELECT * FROM orders WHERE user_id = ? ORDER BY created_at DESC, id DESC')
    .all(userId) as any[];
  const ordersWithItems = orders.map((o) => ({
    ...o,
    items: db
      .prepare(
        "SELECT oi.*, p.slug as product_slug, p.image_key as product_image_key, p.category as product_category, CASE WHEN p.category = 'roasted_beans' OR (p.pricing_tiers_json IS NOT NULL AND p.pricing_tiers_json != '[]' AND p.pricing_tiers_json != '') THEN 'kg' ELSE 'unit' END as unit FROM order_items oi LEFT JOIN products p ON oi.product_id = p.id WHERE oi.order_id = ?"
      )
      .all(o.id),
    gift_dispatches: maskGiftDispatches(
      db.prepare('SELECT * FROM gift_voucher_dispatches WHERE order_id = ? ORDER BY id ASC').all(o.id) as any[]
    ),
  }));
  const now = new Date().toISOString().slice(0, 10);
  const activeVouchers = db
    .prepare('SELECT * FROM promotions WHERE active = 1 AND start_date <= ? AND end_date >= ? ORDER BY id DESC')
    .all(now, now);
  const tiers = db.prepare('SELECT * FROM membership_tiers ORDER BY min_spend_vnd ASC').all();
  const loyaltySettings = db.prepare('SELECT * FROM loyalty_settings WHERE id = 1').get();
  const notifications = db
    .prepare('SELECT * FROM user_notifications WHERE user_id = ? ORDER BY created_at DESC, id DESC LIMIT 40')
    .all(userId);
  const unreadNotifications = (
    db.prepare('SELECT COUNT(*) as c FROM user_notifications WHERE user_id = ? AND is_read = 0').get(userId) as { c: number }
  ).c;

  res.json({
    user: {
      ...user,
      tier: syncedTier,
      addresses: JSON.parse(user.addresses_json || '[]'),
      notificationPrefs: JSON.parse(user.notification_prefs_json || '{}'),
      privacyPrefs: JSON.parse(user.privacy_prefs_json || '{}'),
    },
    points,
    ledger,
    orders: ordersWithItems,
    activeVouchers,
    tiers,
    loyaltySettings,
    notifications,
    unreadNotifications,
  });
});

app.post('/api/account/notifications/read', requireAuth, (req: AuthedRequest, res) => {
  const userId = req.authUser!.userId;
  const { notificationId } = req.body || {};
  if (notificationId) {
    db.prepare('UPDATE user_notifications SET is_read = 1 WHERE id = ? AND user_id = ?').run(Number(notificationId), userId);
  } else {
    db.prepare('UPDATE user_notifications SET is_read = 1 WHERE user_id = ?').run(userId);
  }
  const unreadRow = db
    .prepare('SELECT COUNT(*) as c FROM user_notifications WHERE user_id = ? AND is_read = 0')
    .get(userId) as { c: number };
  res.json({ ok: true, unreadNotifications: unreadRow.c });
});

// ---------- PUBLIC STOREFRONT & CATALOG ----------
app.get('/api/site-bootstrap', (_req, res) => {
  const settingsRows = db.prepare('SELECT key, value FROM site_settings').all() as Array<{ key: string; value: string }>;
  const settings: Record<string, string> = {};
  for (const row of settingsRows) settings[row.key] = row.value;

  const personalities = db.prepare('SELECT * FROM personalities ORDER BY sort_order ASC').all();
  const origins = db.prepare('SELECT * FROM coffee_origins ORDER BY id ASC').all().map((o: any) => ({
    ...o,
    related_skus: JSON.parse(o.related_skus_json || '[]'),
  }));
  const tiers = db.prepare('SELECT * FROM membership_tiers ORDER BY min_spend_vnd ASC').all();
  const loyaltySettings = db.prepare('SELECT * FROM loyalty_settings WHERE id = 1').get();
  const pageRows = db.prepare('SELECT * FROM cms_pages ORDER BY slug ASC').all() as any[];
  const cmsPages: Record<string, any> = {};
  for (const p of pageRows) {
    let sections = [];
    try {
      sections = JSON.parse(p.sections_json || '[]');
    } catch {
      sections = [];
    }
    cmsPages[p.slug] = { ...p, sections };
  }

  res.json({ settings, personalities, origins, tiers, loyaltySettings, cmsPages });
});

app.get('/api/exchange-rate/vietcombank', async (req, res) => {
  const modeParam = req.query.mode;
  const modeOverride: VcbRateMode | undefined =
    modeParam === 'buy' || modeParam === 'transfer' || modeParam === 'sell' ? modeParam : undefined;
  const rate = await getVietcombankUsdRate(db, {
    force: req.query.refresh === '1',
    modeOverride,
  });
  res.json({ rate });
});

app.get('/api/pages/:slug', (req, res) => {
  const p = db.prepare('SELECT * FROM cms_pages WHERE slug = ?').get(req.params.slug) as any;
  if (!p) {
    res.status(404).json({ error: 'Page not found' });
    return;
  }
  let sections = [];
  try {
    sections = JSON.parse(p.sections_json || '[]');
  } catch {
    sections = [];
  }
  res.json({ page: { ...p, sections } });
});

app.get('/api/products', (req, res) => {
  const { category, search, screen, processing, coffee_type, mascot, status } = req.query;
  let sql = "SELECT * FROM products WHERE status != 'draft'";
  const params: any[] = [];

  if (category && category !== 'all') {
    if (category === 'gift_voucher') {
      sql += " AND (sub_category = 'Gift Voucher' OR slug LIKE 'gift-voucher-%')";
    } else if (category === 'roasted') {
      sql += " AND category = 'roasted' AND COALESCE(sub_category, '') != 'Gift Voucher'";
    } else {
      sql += ' AND category = ?';
      params.push(category);
    }
  }
  if (screen && screen !== 'all') {
    sql += ' AND screen_size = ?';
    params.push(screen);
  }
  if (processing && processing !== 'all') {
    sql += ' AND processing_method = ?';
    params.push(processing);
  }
  if (coffee_type && coffee_type !== 'all') {
    sql += ' AND LOWER(coffee_type) LIKE ?';
    params.push(`%${String(coffee_type).toLowerCase()}%`);
  }
  if (mascot) {
    sql += ' AND mascot_slug = ?';
    params.push(mascot);
  }
  if (status && status !== 'all') {
    sql += ' AND status = ?';
    params.push(status);
  }
  if (search) {
    const q = `%${String(search).trim().toLowerCase()}%`;
    sql += ' AND (LOWER(name_vi) LIKE ? OR LOWER(name_en) LIKE ? OR LOWER(sku) LIKE ? OR LOWER(barcode) LIKE ? OR LOWER(sub_category) LIKE ? OR LOWER(grading_spec) LIKE ? OR LOWER(coffee_type) LIKE ? OR LOWER(origin_region) LIKE ?)';
    params.push(q, q, q, q, q, q, q, q);
  }

  sql += ' ORDER BY featured DESC, id ASC';
  const rows = db.prepare(sql).all(...params) as any[];
  const products = rows.map((p) => ({
    ...p,
    barcode: p.barcode || '',
    blend_summary_vi: p.blend_public ? p.blend_summary_vi : 'Tỷ lệ phối trộn bảo mật nội bộ',
    blend_summary_en: p.blend_public ? p.blend_summary_en : 'Confidential proprietary blend ratio',
    brewing_methods: JSON.parse(p.brewing_methods_json || '[]'),
    variants: JSON.parse(p.variants_json || '[]'),
    pricing_tiers: JSON.parse(p.pricing_tiers_json || '[]'),
    packaging_options: JSON.parse(p.packaging_options_json || '[]'),
    gallery_images: JSON.parse(p.gallery_images_json || '[]'),
  }));
  res.json({ products });
});

app.get('/api/products/:slug', (req, res) => {
  const p = db.prepare("SELECT * FROM products WHERE slug = ? AND status != 'draft'").get(req.params.slug) as any;
  if (!p) {
    res.status(404).json({ error: 'Product not found' });
    return;
  }
  const reviews = db
    .prepare('SELECT * FROM product_reviews WHERE product_id = ? ORDER BY created_at DESC')
    .all(p.id);
  const related = db
    .prepare("SELECT * FROM products WHERE category = ? AND id != ? AND status != 'draft' LIMIT 4")
    .all(p.category, p.id) as any[];

  res.json({
    product: {
      ...p,
      barcode: p.barcode || '',
      blend_summary_vi: p.blend_public ? p.blend_summary_vi : 'Tỷ lệ phối trộn bảo mật nội bộ',
      blend_summary_en: p.blend_public ? p.blend_summary_en : 'Confidential proprietary blend ratio',
      brewing_methods: JSON.parse(p.brewing_methods_json || '[]'),
      variants: JSON.parse(p.variants_json || '[]'),
      pricing_tiers: JSON.parse(p.pricing_tiers_json || '[]'),
      packaging_options: JSON.parse(p.packaging_options_json || '[]'),
      gallery_images: JSON.parse(p.gallery_images_json || '[]'),
    },
    reviews,
    related: related.map((r) => ({
      ...r,
      barcode: r.barcode || '',
      variants: JSON.parse(r.variants_json || '[]'),
      pricing_tiers: JSON.parse(r.pricing_tiers_json || '[]'),
      gallery_images: JSON.parse(r.gallery_images_json || '[]'),
    })),
  });
});

app.post('/api/products/:slug/reviews', requireAuth, (req: AuthedRequest, res) => {
  const { rating, comment } = req.body || {};
  const product = db.prepare('SELECT id FROM products WHERE slug = ?').get(req.params.slug) as { id: number } | undefined;
  if (!product) {
    res.status(404).json({ error: 'Product not found' });
    return;
  }
  const r = Number(rating);
  if (!Number.isInteger(r) || r < 1 || r > 5 || !comment || String(comment).trim().length < 5) {
    res.status(400).json({ error: 'Valid rating (1-5) and comment required' });
    return;
  }
  const user = db.prepare('SELECT full_name FROM users WHERE id = ?').get(req.authUser!.userId) as { full_name: string };
  const verifiedOrder = db
    .prepare(`
      SELECT o.id FROM orders o
      JOIN order_items oi ON oi.order_id = o.id
      WHERE o.user_id = ? AND oi.product_id = ? AND o.order_status = 'Completed'
      LIMIT 1
    `)
    .get(req.authUser!.userId, product.id);

  db.prepare(`
    INSERT INTO product_reviews (product_id, user_id, author_name, rating, comment, verified_purchase)
    VALUES (?, ?, ?, ?, ?, ?)
  `).run(product.id, req.authUser!.userId, user.full_name, r, String(comment).trim(), verifiedOrder ? 1 : 0);

  res.status(201).json({ ok: true });
});

// ---------- PROMOTIONS ----------
app.get('/api/promotions', (_req, res) => {
  const today = new Date().toISOString().slice(0, 10);
  const rows = db
    .prepare('SELECT * FROM promotions WHERE active = 1 AND start_date <= ? AND end_date >= ? AND used_count < usage_limit ORDER BY id DESC')
    .all(today, today);
  res.json({ promotions: rows });
});

function maskGiftDispatches(rows: any[]): any[] {
  return rows.map((row) =>
    row && row.status === 'pending_payment'
      ? { ...row, voucher_code: 'ROAR-GIFT-••••-••••', is_code_masked: true }
      : { ...row, is_code_masked: false }
  );
}

function generateGiftVoucherCode(): string {
  const alphabet = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  const makeSeg = () => {
    const bytes = crypto.randomBytes(4);
    let out = '';
    for (let i = 0; i < 4; i++) {
      out += alphabet[bytes[i] % alphabet.length];
    }
    return out;
  };
  for (let attempt = 0; attempt < 10; attempt++) {
    const code = `ROAR-GIFT-${makeSeg()}-${makeSeg()}`;
    const exists = db.prepare('SELECT id FROM gift_voucher_dispatches WHERE voucher_code = ?').get(code);
    if (!exists) return code;
  }
  return `ROAR-GIFT-${Date.now().toString(36).toUpperCase().slice(-8)}`;
}

app.post('/api/promotions/validate', (req: AuthedRequest, res) => {
  const { code, subtotal } = req.body || {};
  if (!code) {
    res.status(400).json({ error: 'Promo code required' });
    return;
  }
  const normalizedCode = String(code).trim().toUpperCase();
  const giftDispatch = db
    .prepare('SELECT * FROM gift_voucher_dispatches WHERE UPPER(voucher_code) = ?')
    .get(normalizedCode) as any;

  if (giftDispatch) {
    if (giftDispatch.status === 'pending_payment') {
      res.status(400).json({ error: 'E-Voucher quà tặng đang chờ xác nhận thanh toán để kích hoạt.' });
      return;
    }
    if (giftDispatch.status === 'redeemed') {
      res.status(400).json({ error: 'Mã E-Voucher quà tặng này đã được sử dụng trước đó.' });
      return;
    }
    if (giftDispatch.status === 'cancelled' || giftDispatch.status === 'expired' || new Date(giftDispatch.expires_at).getTime() < Date.now()) {
      res.status(400).json({ error: 'Mã E-Voucher quà tặng đã hết hạn hoặc đã bị hủy.' });
      return;
    }
    const sub = Number(subtotal || 0);
    const discountAmount = Math.min(sub > 0 ? sub : giftDispatch.face_value_vnd, Number(giftDispatch.face_value_vnd || 0));
    res.json({
      valid: true,
      isGiftVoucher: true,
      promo: {
        id: giftDispatch.id,
        code: giftDispatch.voucher_code,
        discount_type: 'fixed',
        discount_value: giftDispatch.face_value_vnd,
        title_vi: `Phiếu Quà Tặng ROAR E-Voucher (${Number(giftDispatch.face_value_vnd).toLocaleString('vi-VN')}₫)`,
        title_en: `ROAR Digital Gift Voucher (${Number(giftDispatch.face_value_vnd).toLocaleString('en-US')} VND)`,
        terms_vi: `Áp dụng cho ${giftDispatch.recipient_name}. Hạn dùng tới ${String(giftDispatch.expires_at).slice(0, 10)}.`,
        terms_en: `Issued for ${giftDispatch.recipient_name}. Valid until ${String(giftDispatch.expires_at).slice(0, 10)}.`,
      },
      discountAmount,
    });
    return;
  }

  const today = new Date().toISOString().slice(0, 10);
  const promo = db
    .prepare('SELECT * FROM promotions WHERE UPPER(code) = ? AND active = 1 AND start_date <= ? AND end_date >= ?')
    .get(normalizedCode, today, today) as any;

  if (!promo) {
    res.status(404).json({ error: 'Promotion code not found or expired' });
    return;
  }
  if (promo.used_count >= promo.usage_limit) {
    res.status(400).json({ error: 'Promotion usage limit reached' });
    return;
  }
  if (Number(subtotal || 0) < promo.min_order_value) {
    res.status(400).json({ error: `Minimum order value of ${promo.min_order_value.toLocaleString()} VND required` });
    return;
  }
  if (promo.member_only && !req.authUser) {
    res.status(401).json({ error: 'Sign in as a ROAR Member to redeem this voucher' });
    return;
  }

  let discount = 0;
  const sub = Number(subtotal || 0);
  if (promo.discount_type === 'percent') {
    discount = Math.round((sub * promo.discount_value) / 100);
    if (promo.max_discount > 0) discount = Math.min(discount, promo.max_discount);
  } else if (promo.discount_type === 'fixed') {
    discount = promo.discount_value;
  } else if (promo.discount_type === 'free_shipping') {
    discount = promo.discount_value;
  }

  res.json({ valid: true, promo, discountAmount: discount });
});

// ---------- CUSTOMER AUTO-REGISTRATION HELPERS ----------
function normalizeMemberPhoneKey(raw: string): string {
  const digits = String(raw || '').replace(/\D/g, '');
  if (!digits) return '';
  if (digits.startsWith('84') && digits.length >= 10) return `0${digits.slice(2)}`;
  return digits;
}

interface ResolvedOrderCustomer {
  id: number;
  email: string;
  fullName: string;
  phone: string;
  memberCode: string;
  tier: string;
  isNewMember: boolean;
  matchedExisting: boolean;
  welcomePoints: number;
}

function resolveOrCreateOrderCustomer(params: {
  authUser?: { userId: number; email: string; role: string } | null;
  customerName: string;
  customerEmail: string;
  customerPhone: string;
  sourceLabelVi?: string;
  sourceLabelEn?: string;
}): ResolvedOrderCustomer {
  const cleanName = String(params.customerName || '').trim() || 'ROAR Customer';
  const cleanEmail = String(params.customerEmail || '').trim().toLowerCase();
  const cleanPhone = String(params.customerPhone || '').trim();
  const phoneKey = normalizeMemberPhoneKey(cleanPhone);

  let authUserRow: any = null;
  if (params.authUser?.userId) {
    authUserRow = db
      .prepare('SELECT id, email, full_name, phone, role, member_code, tier FROM users WHERE id = ?')
      .get(params.authUser.userId);
  }

  const authEmail = String(authUserRow?.email || '').toLowerCase();
  const authPhoneKey = normalizeMemberPhoneKey(String(authUserRow?.phone || ''));
  // Only bind directly to session user if non-admin OR email/phone matches session user
  const shouldUseSessionUser =
    Boolean(authUserRow) &&
    (authUserRow.role !== 'admin' ||
      (cleanEmail ? cleanEmail === authEmail : !phoneKey || phoneKey === authPhoneKey));

  if (shouldUseSessionUser && authUserRow) {
    if (cleanPhone && !String(authUserRow.phone || '').trim()) {
      db.prepare('UPDATE users SET phone = ? WHERE id = ?').run(cleanPhone, authUserRow.id);
    }
    return {
      id: Number(authUserRow.id),
      email: authUserRow.email,
      fullName: authUserRow.full_name || cleanName,
      phone: cleanPhone || authUserRow.phone || '',
      memberCode: authUserRow.member_code,
      tier: authUserRow.tier,
      isNewMember: false,
      matchedExisting: true,
      welcomePoints: 0,
    };
  }

  let existingUser: any = null;
  if (cleanEmail) {
    existingUser = db
      .prepare('SELECT id, email, full_name, phone, member_code, tier FROM users WHERE LOWER(TRIM(email)) = ?')
      .get(cleanEmail);
  }
  if (!existingUser && phoneKey.length >= 8) {
    const candidates = db
      .prepare("SELECT id, email, full_name, phone, member_code, tier FROM users WHERE phone IS NOT NULL AND TRIM(phone) != ''")
      .all() as any[];
    existingUser = candidates.find((u) => normalizeMemberPhoneKey(u.phone) === phoneKey) || null;
  }

  if (existingUser) {
    if (cleanPhone && !String(existingUser.phone || '').trim()) {
      db.prepare('UPDATE users SET phone = ? WHERE id = ?').run(cleanPhone, existingUser.id);
    }
    if (cleanEmail) {
      db.prepare('UPDATE orders SET user_id = ? WHERE user_id IS NULL AND LOWER(TRIM(customer_email)) = ?').run(
        Number(existingUser.id),
        cleanEmail
      );
    }
    return {
      id: Number(existingUser.id),
      email: existingUser.email,
      fullName: existingUser.full_name || cleanName,
      phone: cleanPhone || existingUser.phone || '',
      memberCode: existingUser.member_code,
      tier: existingUser.tier,
      isNewMember: false,
      matchedExisting: true,
      welcomePoints: 0,
    };
  }

  let memberCode = `RC-MEM-${Math.floor(100000 + Math.random() * 900000)}`;
  for (let attempt = 0; attempt < 6; attempt++) {
    const existsCode = db.prepare('SELECT id FROM users WHERE member_code = ?').get(memberCode);
    if (!existsCode) break;
    memberCode = `RC-MEM-${Math.floor(100000 + Math.random() * 900000)}`;
  }

  const memberEmail = cleanEmail || `${phoneKey || `guest${Date.now()}`}@member.roarcoffee.vn`;
  const randomPasswordHash = hashPassword(crypto.randomBytes(24).toString('hex'));
  const ins = db
    .prepare(`
      INSERT INTO users (email, password_hash, full_name, phone, role, member_code, tier, email_verified)
      VALUES (?, ?, ?, ?, 'customer', ?, 'ROAR Member', 0)
    `)
    .run(memberEmail, randomPasswordHash, cleanName, cleanPhone, memberCode);
  const newUserId = Number(ins.lastInsertRowid);
  const welcomePts = 50;

  db.prepare(`
    INSERT INTO points_ledger (user_id, entry_type, points, description_vi, description_en)
    VALUES (?, 'earn_available', ?, ?, ?)
  `).run(
    newUserId,
    welcomePts,
    params.sourceLabelVi || 'Quà chào mừng thành viên mới ROAR CLUB khi đặt đơn hàng đầu tiên',
    params.sourceLabelEn || 'ROAR CLUB welcome bonus points on first order'
  );

  createUserNotification(newUserId, {
    titleVi: `Chào mừng ${cleanName} gia nhập ROAR CLUB!`,
    titleEn: `Welcome ${cleanName} to ROAR CLUB!`,
    messageVi: `Tài khoản thành viên ${memberCode} đã được khởi tạo tự động kèm ${welcomePts} điểm thưởng chào mừng.`,
    messageEn: `Your ROAR Member account (${memberCode}) is now active with ${welcomePts} welcome points.`,
    category: 'loyalty',
    linkUrl: '/account?tab=rewards',
  });

  if (cleanEmail) {
    db.prepare('UPDATE orders SET user_id = ? WHERE user_id IS NULL AND LOWER(TRIM(customer_email)) = ?').run(
      newUserId,
      cleanEmail
    );
  }

  return {
    id: newUserId,
    email: memberEmail,
    fullName: cleanName,
    phone: cleanPhone,
    memberCode,
    tier: 'ROAR Member',
    isNewMember: true,
    matchedExisting: false,
    welcomePoints: welcomePts,
  };
}

function syncUnlinkedOrderCustomers(): void {
  const unlinked = db
    .prepare(
      "SELECT id, customer_name, customer_email, customer_phone FROM orders WHERE user_id IS NULL ORDER BY id ASC"
    )
    .all() as Array<{ id: number; customer_name: string; customer_email: string; customer_phone: string }>;
  if (unlinked.length === 0) return;
  const tx = db.transaction(() => {
    for (const o of unlinked) {
      if (!String(o.customer_email || '').trim() && !String(o.customer_phone || '').trim()) continue;
      const customer = resolveOrCreateOrderCustomer({
        customerName: o.customer_name || 'ROAR Customer',
        customerEmail: o.customer_email || '',
        customerPhone: o.customer_phone || '',
      });
      db.prepare('UPDATE orders SET user_id = ? WHERE id = ? AND user_id IS NULL').run(customer.id, o.id);
    }
  });
  tx();
}

// ---------- CHECKOUT & ORDERS ----------
app.post('/api/orders', (req: AuthedRequest, res) => {
  const {
    customerName,
    customerEmail,
    customerPhone,
    shippingAddress,
    currency = 'VND',
    items,
    voucherCode,
    pointsToRedeem = 0,
    paymentMethod,
    notes = '',
  } = req.body || {};

  if (!customerName || !customerEmail || !customerPhone || !shippingAddress || !Array.isArray(items) || items.length === 0) {
    res.status(400).json({ error: 'Missing required checkout details or items' });
    return;
  }

  const createOrderTx = db.transaction(() => {
    const customerRecord = resolveOrCreateOrderCustomer({
      authUser: req.authUser || null,
      customerName: String(customerName).trim(),
      customerEmail: String(customerEmail).trim().toLowerCase(),
      customerPhone: String(customerPhone).trim(),
    });
    const effectiveUserId = customerRecord.id;

    let subtotal = 0;
    const resolvedItems: Array<{
      productId: number;
      sku: string;
      nameVi: string;
      nameEn: string;
      variantLabel: string;
      quantity: number;
      unitPriceVnd: number;
      lineTotalVnd: number;
    }> = [];

    for (const item of items) {
      const product = db.prepare('SELECT * FROM products WHERE id = ?').get(Number(item.productId)) as any;
      if (!product) throw new Error('Product not found in catalog');
      const qty = Math.max(1, Number(item.quantity || 1));
      const pricingTiers = JSON.parse(product.pricing_tiers_json || '[]');
      const variants = JSON.parse(product.variants_json || '[]') as Array<{ label: string; priceVnd: number }>;

      let unitPriceVnd = product.price_vnd;
      let variantLabel = String(item.variantLabel || 'Standard');

      if (Array.isArray(pricingTiers) && pricingTiers.length > 0) {
        const tier = resolveVolumeTier(pricingTiers, qty);
        if (tier) {
          unitPriceVnd = tier.priceVnd;
          variantLabel = `${qty} kg (${tier.labelVi})`;
        } else {
          variantLabel = `${qty} kg`;
        }
      } else {
        const matchedVariant = variants.find((v) => v.label === item.variantLabel);
        unitPriceVnd = matchedVariant ? matchedVariant.priceVnd : product.price_vnd;
        variantLabel = matchedVariant ? matchedVariant.label : String(item.variantLabel || 'Standard');
      }

      const lineTotalVnd = unitPriceVnd * qty;
      subtotal += lineTotalVnd;
      resolvedItems.push({
        productId: product.id,
        sku: product.sku,
        nameVi: product.name_vi,
        nameEn: product.name_en,
        variantLabel,
        quantity: qty,
        unitPriceVnd,
        lineTotalVnd,
      });

      if (product.inventory > 0) {
        db.prepare('UPDATE products SET inventory = MAX(0, inventory - ?) WHERE id = ?').run(qty, product.id);
      }
    }

    const shippingRow = db.prepare("SELECT value FROM site_settings WHERE key = 'shipping_rules_json'").get() as
      | { value: string }
      | undefined;
    const baseShippingFee = calculateShippingFee(subtotal, {
      shipping_rules_json: shippingRow?.value || '',
    }).feeVnd;
    let shippingFee = baseShippingFee;
    let discountAmount = 0;
    let appliedVoucher = '';
    let redeemedGiftDispatchId: number | null = null;

    if (voucherCode) {
      const normalizedCode = String(voucherCode).trim().toUpperCase();
      const today = new Date().toISOString().slice(0, 10);
      const giftDispatch = db
        .prepare("SELECT * FROM gift_voucher_dispatches WHERE UPPER(voucher_code) = ? AND status = 'active' AND expires_at >= datetime('now')")
        .get(normalizedCode) as any;

      if (giftDispatch) {
        appliedVoucher = giftDispatch.voucher_code;
        discountAmount = Math.min(subtotal, Number(giftDispatch.face_value_vnd || 0));
        redeemedGiftDispatchId = Number(giftDispatch.id);
      } else {
        const promo = db
          .prepare('SELECT * FROM promotions WHERE UPPER(code) = ? AND active = 1 AND start_date <= ? AND end_date >= ? AND used_count < usage_limit')
          .get(normalizedCode, today, today) as any;
        if (promo && subtotal >= promo.min_order_value && (!promo.member_only || req.authUser)) {
          appliedVoucher = promo.code;
          if (promo.discount_type === 'percent') {
            discountAmount = Math.round((subtotal * promo.discount_value) / 100);
            if (promo.max_discount > 0) discountAmount = Math.min(discountAmount, promo.max_discount);
          } else if (promo.discount_type === 'fixed') {
            discountAmount = Math.min(subtotal, promo.discount_value);
          } else if (promo.discount_type === 'free_shipping') {
            shippingFee = 0;
          }
          db.prepare('UPDATE promotions SET used_count = used_count + 1 WHERE id = ?').run(promo.id);
        }
      }
    }

    let pointsRedeemed = 0;
    let pointsDiscount = 0;
    const requestedPoints = Math.max(0, Math.floor(Number(pointsToRedeem || 0)));

    if (requestedPoints > 0 && req.authUser) {
      const loyalty = db.prepare('SELECT * FROM loyalty_settings WHERE id = 1').get() as any;
      const summary = getPointsSummary(req.authUser.userId);
      const maxDiscountVnd = Math.floor((subtotal * (loyalty?.max_redeem_percent || 30)) / 100);
      const maxPointsByRule = Math.floor(maxDiscountVnd / (loyalty?.vnd_per_point || 100));
      pointsRedeemed = Math.min(requestedPoints, summary.available, maxPointsByRule);
      pointsDiscount = pointsRedeemed * (loyalty?.vnd_per_point || 100);
    }

    const total = Math.max(0, subtotal - discountAmount - pointsDiscount + shippingFee);
    const orderNumber = `RC-${new Date().toISOString().slice(0, 10).replace(/-/g, '')}-${Math.floor(1000 + Math.random() * 9000)}`;

    let initialPaymentStatus = 'awaiting_payment';
    if (paymentMethod === 'wallet') {
      if (!req.authUser) {
        throw new Error('Vui lòng đăng nhập để thanh toán bằng Ví Thành viên ROAR.');
      }
      const uWallet = db.prepare('SELECT wallet_balance_vnd FROM users WHERE id = ?').get(req.authUser.userId) as any;
      const currentBal = Number(uWallet?.wallet_balance_vnd || 0);
      if (currentBal < total) {
        throw new Error(`Số dư Ví ROAR (${currentBal.toLocaleString('vi-VN')}₫) không đủ để thanh toán đơn hàng ${total.toLocaleString('vi-VN')}₫.`);
      }
      db.prepare('UPDATE users SET wallet_balance_vnd = wallet_balance_vnd - ? WHERE id = ?').run(total, req.authUser.userId);
      db.prepare(`
        INSERT INTO wallet_transactions (user_id, tx_type, amount_vnd, bonus_vnd, bonus_pct, points_delta, note, reference_code)
        VALUES (?, 'spend', ?, 0, 0, 0, ?, ?)
      `).run(
        req.authUser.userId,
        -total,
        `Thanh toán đơn hàng ${orderNumber}`,
        orderNumber
      );
      initialPaymentStatus = 'paid';
    } else if (paymentMethod === 'points') {
      if (!req.authUser) {
        throw new Error('Vui lòng đăng nhập để mua hàng bằng Điểm thưởng ROAR.');
      }
      const loyalty = db.prepare('SELECT * FROM loyalty_settings WHERE id = 1').get() as any;
      const vndPerPoint = Number(loyalty?.vnd_per_point || 100);
      const summary = getPointsSummary(req.authUser.userId);
      const pointsNeeded = Math.ceil(total / vndPerPoint);
      if (summary.available < pointsNeeded) {
        throw new Error(`Bạn cần ${pointsNeeded.toLocaleString('vi-VN')} điểm để thanh toán đơn này (hiện có ${summary.available.toLocaleString('vi-VN')} điểm).`);
      }
      pointsRedeemed += pointsNeeded;
      pointsDiscount += total;
      initialPaymentStatus = 'paid';
    }

    const orderResult = db
      .prepare(`
        INSERT INTO orders (
          order_number, user_id, customer_name, customer_email, customer_phone, shipping_address,
          currency, subtotal, discount_amount, points_redeemed, points_discount, shipping_fee, total,
          voucher_code, payment_method, payment_status, order_status, notes
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'Pending', ?)
      `)
      .run(
        orderNumber,
        effectiveUserId,
        String(customerName).trim(),
        String(customerEmail).trim().toLowerCase(),
        String(customerPhone).trim(),
        String(shippingAddress).trim(),
        currency || 'VND',
        subtotal,
        discountAmount,
        pointsRedeemed,
        pointsDiscount,
        shippingFee,
        total,
        appliedVoucher,
        paymentMethod || 'cod',
        initialPaymentStatus,
        String(notes || '').trim()
      );

    const orderId = Number(orderResult.lastInsertRowid);
    if (redeemedGiftDispatchId) {
      const upd = db
        .prepare("UPDATE gift_voucher_dispatches SET status = 'redeemed', redeemed_order_id = ?, redeemed_at = datetime('now') WHERE id = ? AND status = 'active'")
        .run(orderId, redeemedGiftDispatchId);
      if (upd.changes !== 1) {
        throw new Error('Gift voucher was already redeemed');
      }
    }
    const insertItem = db.prepare(`
      INSERT INTO order_items (order_id, product_id, sku, product_name_vi, product_name_en, variant_label, quantity, unit_price_vnd, line_total_vnd)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    for (const ri of resolvedItems) {
      insertItem.run(orderId, ri.productId, ri.sku, ri.nameVi, ri.nameEn, ri.variantLabel, ri.quantity, ri.unitPriceVnd, ri.lineTotalVnd);
    }

    if (pointsRedeemed > 0 && req.authUser) {
      db.prepare(`
        INSERT INTO points_ledger (user_id, order_id, entry_type, points, description_vi, description_en)
        VALUES (?, ?, 'redeem', ?, ?, ?)
      `).run(
        req.authUser.userId,
        orderId,
        -pointsRedeemed,
        `Quy đổi ${pointsRedeemed} điểm cho đơn hàng ${orderNumber}`,
        `Redeemed ${pointsRedeemed} points on order ${orderNumber}`
      );
    }

    const loyalty = db.prepare('SELECT * FROM loyalty_settings WHERE id = 1').get() as any;
    const syncedCustomerTier = syncUserTierInDb(effectiveUserId);
    const tierRow = db.prepare('SELECT point_multiplier FROM membership_tiers WHERE name = ?').get(syncedCustomerTier) as { point_multiplier: number } | undefined;
    const mult = tierRow?.point_multiplier || 1.0;
    const netEligible = Math.max(0, subtotal - discountAmount - pointsDiscount);
    const pendingPoints = Math.floor((netEligible / 10000) * (loyalty?.points_per_10k_vnd || 1) * mult);
    if (pendingPoints > 0) {
      db.prepare(`
        INSERT INTO points_ledger (user_id, order_id, entry_type, points, description_vi, description_en)
        VALUES (?, ?, 'earn_pending', ?, ?, ?)
      `).run(
        effectiveUserId,
        orderId,
        pendingPoints,
        `Điểm chờ duyệt từ đơn hàng ${orderNumber} (Cộng chính thức khi hoàn tất)`,
        `Pending points for order ${orderNumber} (Credited upon completion)`
      );
    }

    createUserNotification(effectiveUserId, {
      titleVi: `Đã tiếp nhận đơn hàng ${orderNumber}`,
      titleEn: `Order ${orderNumber} received`,
      messageVi: `Đơn hàng trị giá ${total.toLocaleString('vi-VN')} ₫ đang chờ Quản trị viên ROAR xác nhận và chuẩn bị hàng.`,
      messageEn: `Your order totaling ${total.toLocaleString('en-US')} VND is awaiting confirmation and preparation.`,
      category: 'order',
      linkUrl: '/account?tab=orders',
    });

    return {
      order: {
        orderId,
        orderNumber,
        total,
        subtotal,
        discountAmount,
        pointsDiscount,
        shippingFee,
        paymentMethod: String(paymentMethod || 'cod'),
        customerEmail: String(customerEmail).trim().toLowerCase(),
      },
      membership: {
        isNewMember: customerRecord.isNewMember,
        matchedExisting: customerRecord.matchedExisting,
        memberCode: customerRecord.memberCode,
        tier: customerRecord.tier,
        fullName: customerRecord.fullName,
        welcomePoints: customerRecord.welcomePoints,
      },
      newCustomerRecord: customerRecord.isNewMember ? customerRecord : null,
    };
  });

  try {
    const created = createOrderTx();
    let authPayload: { token: string; user: any } | undefined;
    if (!req.authUser && created.newCustomerRecord) {
      const m = created.newCustomerRecord;
      const token = signSessionToken({ userId: m.id, email: m.email, role: 'customer' });
      setSessionCookie(req, res, token);
      authPayload = {
        token,
        user: {
          id: m.id,
          email: m.email,
          fullName: m.fullName,
          phone: m.phone,
          role: 'customer',
          memberCode: m.memberCode,
          tier: m.tier,
          emailVerified: false,
          points: { available: m.welcomePoints, pending: 0, redeemed: 0, expired: 0, expiringSoon: 0 },
          walletBalanceVnd: 0,
        },
      };
    }
    dispatchOrderConfirmationEmail({
      customerEmail: created.order.customerEmail,
      customerName: String(customerName).trim(),
      orderNumber: created.order.orderNumber,
      totalVnd: created.order.total,
      paymentMethod: created.order.paymentMethod,
      memberCode: created.membership?.memberCode,
    });
    res.status(201).json({
      ok: true,
      order: created.order,
      membership: created.membership,
      ...(authPayload ? { auth: authPayload } : {}),
    });
  } catch (err: any) {
    res.status(400).json({ error: err.message || 'Unable to create order' });
  }
});

// ---------- GIFTPOP-STYLE GIFT VOUCHER CHECKOUT & DISPATCH ----------

app.post('/api/gift-vouchers/checkout', (req: AuthedRequest, res) => {
  const {
    productId,
    productSlug = '',
    purchaseMode = 'gift',
    deliveryChannel = 'zalo_sms',
    senderName,
    senderEmail = '',
    senderPhone = '',
    recipients = [],
    selfQuantity = 1,
    giftMessage = '',
    promoCode = '',
    pointsToRedeem = 0,
    paymentMethod = 'vietqr',
  } = req.body || {};

  const mode = purchaseMode === 'self' ? 'self' : 'gift';
  const channel = deliveryChannel === 'email' ? 'email' : 'zalo_sms';

  let product = db.prepare('SELECT * FROM products WHERE id = ?').get(Number(productId)) as any;
  if (!product && productSlug) {
    product = db.prepare('SELECT * FROM products WHERE slug = ?').get(String(productSlug).trim()) as any;
  }
  if (!product || (product.sub_category !== 'Gift Voucher' && !String(product.slug || '').startsWith('gift-voucher-'))) {
    res.status(404).json({ error: 'Sản phẩm Gift Voucher không tồn tại' });
    return;
  }

  let authUserRow: any = null;
  if (req.authUser) {
    authUserRow = db.prepare('SELECT id, full_name, email, phone, member_code, tier, wallet_balance_vnd FROM users WHERE id = ?').get(req.authUser.userId);
  }

  const finalSenderName = String(senderName || authUserRow?.full_name || '').trim();
  const finalSenderEmail = String(senderEmail || authUserRow?.email || '').trim().toLowerCase();
  const finalSenderPhone = String(senderPhone || authUserRow?.phone || '').trim();
  const senderPhoneKey = normalizeMemberPhoneKey(finalSenderPhone);

  if (!finalSenderName || (!finalSenderEmail && !finalSenderPhone)) {
    res.status(400).json({ error: 'Vui lòng nhập họ tên và số điện thoại hoặc email của người mua.' });
    return;
  }
  if (finalSenderEmail && !/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(finalSenderEmail)) {
    res.status(400).json({ error: 'Địa chỉ Email người mua không hợp lệ.' });
    return;
  }

  let normalizedRecipients: Array<{ name: string; contact: string }> = [];
  if (mode === 'self') {
    const qty = Math.min(20, Math.max(1, Math.floor(Number(selfQuantity || 1))));
    const contact = channel === 'email' ? (finalSenderEmail || finalSenderPhone) : (finalSenderPhone || finalSenderEmail);
    if (!contact) {
      res.status(400).json({ error: 'Vui lòng nhập thông tin nhận E-Voucher của bạn.' });
      return;
    }
    for (let i = 0; i < qty; i++) {
      normalizedRecipients.push({ name: finalSenderName, contact });
    }
  } else {
    if (!Array.isArray(recipients) || recipients.length === 0 || recipients.length > 20) {
      res.status(400).json({ error: 'Vui lòng thêm từ 1 đến 20 người nhận Voucher.' });
      return;
    }
    for (const r of recipients) {
      const rName = String(r?.name || '').trim();
      const rContact = String(r?.contact || '').trim();
      if (!rName || !rContact) {
        res.status(400).json({ error: 'Mỗi người nhận cần nhập đầy đủ tên và SĐT Zalo hoặc Email.' });
        return;
      }
      normalizedRecipients.push({ name: rName.slice(0, 80), contact: rContact.slice(0, 120) });
    }
  }

  const cleanGiftMsg = String(giftMessage || '').trim().slice(0, 300);
  const allowedMethods = new Set(['vietqr', 'vnpay_qr', 'zalopay', 'momo', 'shopeepay', 'wallet', 'points']);
  const finalMethod = allowedMethods.has(String(paymentMethod)) ? String(paymentMethod) : 'vietqr';

  const tx = db.transaction(() => {
    const resolvedCustomer = resolveOrCreateOrderCustomer({
      authUser: req.authUser || null,
      customerName: finalSenderName,
      customerEmail: finalSenderEmail,
      customerPhone: finalSenderPhone,
      sourceLabelVi: 'Quà chào mừng thành viên mới ROAR CLUB khi đặt E-Voucher',
      sourceLabelEn: 'ROAR CLUB welcome bonus points on first E-Voucher order',
    });
    const effectiveUserId = resolvedCustomer.id;
    const isNewMember = resolvedCustomer.isNewMember;
    const matchedExisting = resolvedCustomer.matchedExisting;
    const memberRecord = {
      id: resolvedCustomer.id,
      email: resolvedCustomer.email,
      fullName: resolvedCustomer.fullName,
      phone: resolvedCustomer.phone,
      memberCode: resolvedCustomer.memberCode,
      tier: resolvedCustomer.tier,
      welcomePoints: resolvedCustomer.welcomePoints,
    };

    const unitPriceVnd = Number(product.price_vnd || 0);
    const qty = normalizedRecipients.length;
    const subtotal = unitPriceVnd * qty;
    let discountAmount = 0;
    let appliedPromo = '';

    if (promoCode) {
      const normalizedCode = String(promoCode).trim().toUpperCase();
      const today = new Date().toISOString().slice(0, 10);
      const promo = db
        .prepare("SELECT * FROM promotions WHERE UPPER(code) = ? AND active = 1 AND start_date <= ? AND end_date >= ? AND used_count < usage_limit AND discount_type != 'free_shipping'")
        .get(normalizedCode, today, today) as any;
      if (promo && subtotal >= promo.min_order_value && (!promo.member_only || req.authUser)) {
        appliedPromo = promo.code;
        if (promo.discount_type === 'percent') {
          discountAmount = Math.round((subtotal * promo.discount_value) / 100);
          if (promo.max_discount > 0) discountAmount = Math.min(discountAmount, promo.max_discount);
        } else if (promo.discount_type === 'fixed') {
          discountAmount = Math.min(subtotal, promo.discount_value);
        }
        db.prepare('UPDATE promotions SET used_count = used_count + 1 WHERE id = ?').run(promo.id);
      }
    }

    let pointsRedeemed = 0;
    let pointsDiscount = 0;
    const requestedPoints = Math.max(0, Math.floor(Number(pointsToRedeem || 0)));
    if (requestedPoints > 0 && req.authUser) {
      const loyalty = db.prepare('SELECT * FROM loyalty_settings WHERE id = 1').get() as any;
      const summary = getPointsSummary(req.authUser.userId);
      const maxDiscountVnd = Math.floor((subtotal * (loyalty?.max_redeem_percent || 30)) / 100);
      const maxPointsByRule = Math.floor(maxDiscountVnd / (loyalty?.vnd_per_point || 100));
      pointsRedeemed = Math.min(requestedPoints, summary.available, maxPointsByRule);
      pointsDiscount = pointsRedeemed * (loyalty?.vnd_per_point || 100);
    }

    const total = Math.max(0, subtotal - discountAmount - pointsDiscount);
    const orderNumber = `RC-${new Date().toISOString().slice(0, 10).replace(/-/g, '')}-${Math.floor(1000 + Math.random() * 9000)}`;

    let initialPaymentStatus = 'awaiting_payment';
    let initialOrderStatus = 'Pending';
    let dispatchStatus: 'pending_payment' | 'active' = 'pending_payment';

    if (finalMethod === 'wallet') {
      if (!req.authUser) {
        throw new Error('Vui lòng đăng nhập để thanh toán bằng Ví Thành viên ROAR.');
      }
      const uWallet = db.prepare('SELECT wallet_balance_vnd FROM users WHERE id = ?').get(req.authUser.userId) as any;
      const currentBal = Number(uWallet?.wallet_balance_vnd || 0);
      if (currentBal < total) {
        throw new Error(`Số dư Ví ROAR (${currentBal.toLocaleString('vi-VN')}₫) không đủ để thanh toán (${total.toLocaleString('vi-VN')}₫).`);
      }
      db.prepare('UPDATE users SET wallet_balance_vnd = wallet_balance_vnd - ? WHERE id = ?').run(total, req.authUser.userId);
      db.prepare(`
        INSERT INTO wallet_transactions (user_id, tx_type, amount_vnd, bonus_vnd, bonus_pct, points_delta, note, reference_code)
        VALUES (?, 'spend', ?, 0, 0, 0, ?, ?)
      `).run(req.authUser.userId, -total, `Mua / Tặng Gift Voucher ${orderNumber}`, orderNumber);
      initialPaymentStatus = 'paid';
      initialOrderStatus = 'Completed';
      dispatchStatus = 'active';
    } else if (finalMethod === 'points') {
      if (!req.authUser) {
        throw new Error('Vui lòng đăng nhập để đổi bằng Điểm thưởng ROAR.');
      }
      const loyalty = db.prepare('SELECT * FROM loyalty_settings WHERE id = 1').get() as any;
      const vndPerPoint = Number(loyalty?.vnd_per_point || 100);
      const summary = getPointsSummary(req.authUser.userId);
      const pointsNeeded = Math.ceil(total / vndPerPoint);
      if (summary.available < pointsNeeded) {
        throw new Error(`Bạn cần ${pointsNeeded.toLocaleString('vi-VN')} điểm để thanh toán (hiện có ${summary.available.toLocaleString('vi-VN')} điểm).`);
      }
      pointsRedeemed += pointsNeeded;
      pointsDiscount += total;
      initialPaymentStatus = 'paid';
      initialOrderStatus = 'Completed';
      dispatchStatus = 'active';
    } else if (total === 0) {
      initialPaymentStatus = 'paid';
      initialOrderStatus = 'Completed';
      dispatchStatus = 'active';
    }

    const channelLabel = channel === 'email' ? 'Email' : 'SMS / Zalo';
    const shippingSummary = `[E-Voucher Digital Dispatch · ${channelLabel}] ${mode === 'gift' ? `Tặng ${qty} người nhận` : 'Mua cho bản thân'}`;
    const orderNote = [
      `[Giftpop E-Voucher · ${mode === 'gift' ? 'Mua tặng' : 'Mua cho tôi'} · ${channelLabel}]`,
      cleanGiftMsg ? `Lời chúc: "${cleanGiftMsg}"` : '',
      `Người nhận: ${normalizedRecipients.map((r) => `${r.name} (${r.contact})`).join(', ')}`,
    ]
      .filter(Boolean)
      .join(' | ');

    const resolvedOrderEmail =
      finalSenderEmail || memberRecord?.email || `${senderPhoneKey || 'guest'}@member.roarcoffee.vn`;

    const orderInsert = db
      .prepare(`
        INSERT INTO orders (
          order_number, user_id, customer_name, customer_email, customer_phone, shipping_address,
          currency, subtotal, discount_amount, points_redeemed, points_discount, shipping_fee, total,
          voucher_code, payment_method, payment_status, order_status, notes
        ) VALUES (?, ?, ?, ?, ?, ?, 'VND', ?, ?, ?, ?, 0, ?, ?, ?, ?, ?, ?)
      `)
      .run(
        orderNumber,
        effectiveUserId,
        finalSenderName,
        resolvedOrderEmail,
        finalSenderPhone || resolvedOrderEmail,
        shippingSummary,
        subtotal,
        discountAmount,
        pointsRedeemed,
        pointsDiscount,
        total,
        appliedPromo,
        finalMethod,
        initialPaymentStatus,
        initialOrderStatus,
        orderNote
      );

    const orderId = Number(orderInsert.lastInsertRowid);
    db.prepare(`
      INSERT INTO order_items (order_id, product_id, sku, product_name_vi, product_name_en, variant_label, quantity, unit_price_vnd, line_total_vnd)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    `).run(
      orderId,
      product.id,
      product.sku,
      product.name_vi,
      product.name_en,
      `E-Voucher (${unitPriceVnd.toLocaleString('vi-VN')}₫) · ${channelLabel}`,
      qty,
      unitPriceVnd,
      subtotal
    );

    if (pointsRedeemed > 0 && req.authUser) {
      db.prepare(`
        INSERT INTO points_ledger (user_id, order_id, entry_type, points, description_vi, description_en)
        VALUES (?, ?, 'redeem', ?, ?, ?)
      `).run(
        req.authUser.userId,
        orderId,
        -pointsRedeemed,
        `Quy đổi ${pointsRedeemed} điểm cho đơn Gift Voucher ${orderNumber}`,
        `Redeemed ${pointsRedeemed} points on Gift Voucher order ${orderNumber}`
      );
    }

    const expiresAt = new Date(Date.now() + 365 * 24 * 60 * 60 * 1000).toISOString().slice(0, 19).replace('T', ' ');
    const insertDispatch = db.prepare(`
      INSERT INTO gift_voucher_dispatches (
        order_id, order_number, product_id, product_slug, voucher_code, purchase_mode, delivery_channel,
        sender_user_id, sender_name, sender_email, sender_phone, recipient_name, recipient_contact,
        gift_message, face_value_vnd, status, expires_at
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);

    const dispatches: any[] = [];
    for (const r of normalizedRecipients) {
      const voucherCode = generateGiftVoucherCode();
      const ins = insertDispatch.run(
        orderId,
        orderNumber,
        product.id,
        product.slug,
        voucherCode,
        mode,
        channel,
        effectiveUserId,
        finalSenderName,
        resolvedOrderEmail,
        finalSenderPhone,
        r.name,
        r.contact,
        cleanGiftMsg,
        unitPriceVnd,
        dispatchStatus,
        expiresAt
      );
      dispatches.push({
        id: Number(ins.lastInsertRowid),
        order_id: orderId,
        order_number: orderNumber,
        product_id: product.id,
        product_slug: product.slug,
        voucher_code: voucherCode,
        purchase_mode: mode,
        delivery_channel: channel,
        sender_name: finalSenderName,
        recipient_name: r.name,
        recipient_contact: r.contact,
        gift_message: cleanGiftMsg,
        face_value_vnd: unitPriceVnd,
        status: dispatchStatus,
        expires_at: expiresAt,
      });
    }

    if (effectiveUserId) {
      createUserNotification(effectiveUserId, {
        titleVi: dispatchStatus === 'active' ? `Đã kích hoạt ${qty} E-Voucher (${orderNumber})` : `Đã tạo đơn E-Voucher ${orderNumber}`,
        titleEn: dispatchStatus === 'active' ? `Activated ${qty} E-Voucher(s) (${orderNumber})` : `Gift Voucher order ${orderNumber} created`,
        messageVi:
          dispatchStatus === 'active'
            ? `Các mã quà tặng ${dispatches.map((d) => d.voucher_code).join(', ')} đã sẵn sàng gửi đến người nhận.`
            : `Đơn quà tặng trị giá ${total.toLocaleString('vi-VN')}₫ đang chờ xác nhận thanh toán QR để kích hoạt mã.`,
        messageEn:
          dispatchStatus === 'active'
            ? `Voucher codes ${dispatches.map((d) => d.voucher_code).join(', ')} are active and ready to share.`
            : `Gift order totaling ${total.toLocaleString('en-US')} VND is awaiting QR payment verification.`,
        category: 'promo',
        linkUrl: '/account?tab=vouchers',
      });
    }

    return {
      order: {
        orderId,
        orderNumber,
        subtotal,
        discountAmount,
        pointsDiscount,
        shippingFee: 0,
        total,
        paymentMethod: finalMethod,
        paymentStatus: initialPaymentStatus,
        orderStatus: initialOrderStatus,
        customerEmail: resolvedOrderEmail,
        customerPhone: finalSenderPhone,
      },
      dispatches: maskGiftDispatches(dispatches),
      membership: memberRecord
        ? {
            isNewMember,
            matchedExisting,
            memberCode: memberRecord.memberCode,
            tier: memberRecord.tier,
            fullName: memberRecord.fullName,
            email: isNewMember ? memberRecord.email : undefined,
            phone: isNewMember ? memberRecord.phone : undefined,
            welcomePoints: isNewMember ? memberRecord.welcomePoints : 0,
          }
        : { isNewMember: false, matchedExisting: false },
      newMemberRecord: isNewMember ? memberRecord : null,
    };
  });

  try {
    const result = tx();
    let authPayload: { token: string; user: any } | undefined;
    if (!req.authUser && result.newMemberRecord) {
      const m = result.newMemberRecord;
      const token = signSessionToken({ userId: m.id, email: m.email, role: 'customer' });
      setSessionCookie(req, res, token);
      authPayload = {
        token,
        user: {
          id: m.id,
          email: m.email,
          fullName: m.fullName,
          phone: m.phone,
          role: 'customer',
          memberCode: m.memberCode,
          tier: m.tier,
          emailVerified: false,
          points: { available: m.welcomePoints, pending: 0, redeemed: 0, expired: 0, expiringSoon: 0 },
          walletBalanceVnd: 0,
        },
      };
    }
    const { newMemberRecord: _omit, ...publicPayload } = result;
    dispatchOrderConfirmationEmail({
      customerEmail: publicPayload.order.customerEmail,
      customerName: publicPayload.membership?.fullName || finalSenderName,
      orderNumber: publicPayload.order.orderNumber,
      totalVnd: publicPayload.order.total,
      paymentMethod: publicPayload.order.paymentMethod,
      memberCode: publicPayload.membership?.memberCode,
    });
    res.status(201).json({ ok: true, ...publicPayload, ...(authPayload ? { auth: authPayload } : {}) });
  } catch (err: any) {
    res.status(400).json({ error: err.message || 'Không thể khởi tạo đơn Gift Voucher.' });
  }
});

app.get('/api/gift-vouchers/mine', requireAuth, (req: AuthedRequest, res) => {
  const userRow = db.prepare('SELECT id, email, phone FROM users WHERE id = ?').get(req.authUser!.userId) as any;
  const rows = db
    .prepare(`
      SELECT d.*, p.name_vi as product_name_vi, p.name_en as product_name_en, p.image_key as product_image_key
      FROM gift_voucher_dispatches d
      LEFT JOIN products p ON p.id = d.product_id
      WHERE d.sender_user_id = ?
         OR (LOWER(d.sender_email) != '' AND LOWER(d.sender_email) = ?)
         OR (LOWER(d.recipient_contact) != '' AND (LOWER(d.recipient_contact) = ? OR d.recipient_contact = ?))
      ORDER BY d.id DESC
      LIMIT 60
    `)
    .all(
      req.authUser!.userId,
      String(userRow?.email || '').toLowerCase(),
      String(userRow?.email || '').toLowerCase(),
      String(userRow?.phone || '')
    ) as any[];
  res.json({ dispatches: maskGiftDispatches(rows) });
});

app.post('/api/orders/:orderNumber/confirm-payment-reference', (req, res) => {
  const { email, transactionRef = '' } = req.body || {};
  const order = db
    .prepare('SELECT * FROM orders WHERE order_number = ? AND LOWER(customer_email) = ?')
    .get(req.params.orderNumber, String(email || '').trim().toLowerCase()) as any;
  if (!order) {
    res.status(404).json({ error: 'Order not found' });
    return;
  }
  const refNote = transactionRef
    ? ` [Customer QR/Wallet Ref: ${String(transactionRef).trim()}]`
    : ' [Customer reported QR/Wallet transfer completed - pending reconciliation]';
  db.prepare("UPDATE orders SET payment_status = 'pending_verification', notes = notes || ?, updated_at = datetime('now') WHERE id = ?").run(
    refNote,
    order.id
  );
  if (order.user_id) {
    createUserNotification(order.user_id, {
      titleVi: `Đã ghi nhận thanh toán đơn ${order.order_number}`,
      titleEn: `Payment reference logged for ${order.order_number}`,
      messageVi: 'Hệ thống đang đối soát giao dịch QR / Ví điện tử của bạn và sẽ duyệt đơn trong thời gian sớm nhất.',
      messageEn: 'We have logged your QR / e-wallet transfer reference and are verifying your order.',
      category: 'order',
      linkUrl: '/account?tab=orders',
    });
  }
  res.json({ ok: true, paymentStatus: 'pending_verification' });
});

app.get('/api/orders/track', (req, res) => {
  const rawOrderNumber = String(req.query.orderNumber || '').trim();
  const rawPhone = String(req.query.phone || '').trim();
  const rawEmail = String(req.query.email || '').trim().toLowerCase();
  const rawQuery = String(req.query.q || '').trim();

  if (!rawOrderNumber && !rawPhone && !rawEmail && !rawQuery) {
    res.status(400).json({ error: 'Vui lòng nhập Mã đơn hàng, Số điện thoại hoặc Email để tra cứu.' });
    return;
  }

  const normalizeDigits = (val: string) => val.replace(/\D/g, '');
  const buildPhonePatterns = (val: string): string[] => {
    const d = normalizeDigits(val);
    if (!d) return [];
    const candidates = new Set<string>([d]);
    if (d.startsWith('84') && d.length >= 10) {
      candidates.add(`0${d.slice(2)}`);
    } else if (d.startsWith('0') && d.length >= 10) {
      candidates.add(`84${d.slice(1)}`);
    }
    return Array.from(candidates);
  };

  let matchingOrders: any[] = [];
  const phoneNormalizedSql = "REPLACE(REPLACE(REPLACE(REPLACE(REPLACE(customer_phone, ' ', ''), '-', ''), '.', ''), '+', ''), '(', '')";

  if (rawOrderNumber && rawEmail) {
    matchingOrders = db
      .prepare('SELECT * FROM orders WHERE UPPER(TRIM(order_number)) = ? AND LOWER(TRIM(customer_email)) = ? ORDER BY id DESC')
      .all(rawOrderNumber.toUpperCase(), rawEmail) as any[];
  } else if (rawOrderNumber) {
    matchingOrders = db
      .prepare('SELECT * FROM orders WHERE UPPER(TRIM(order_number)) = ? ORDER BY id DESC')
      .all(rawOrderNumber.toUpperCase()) as any[];
  } else if (rawEmail) {
    matchingOrders = db
      .prepare('SELECT * FROM orders WHERE LOWER(TRIM(customer_email)) = ? ORDER BY id DESC LIMIT 20')
      .all(rawEmail) as any[];
  } else if (rawPhone) {
    const patterns = buildPhonePatterns(rawPhone);
    if (patterns.length > 0) {
      const placeholders = patterns.map(() => `${phoneNormalizedSql} = ?`).join(' OR ');
      matchingOrders = db
        .prepare(`SELECT * FROM orders WHERE (${placeholders}) ORDER BY id DESC LIMIT 20`)
        .all(...patterns) as any[];
    }
  } else if (rawQuery) {
    if (rawQuery.includes('@')) {
      matchingOrders = db
        .prepare('SELECT * FROM orders WHERE LOWER(TRIM(customer_email)) = ? ORDER BY id DESC LIMIT 20')
        .all(rawQuery.toLowerCase()) as any[];
    } else {
      const byOrderNo = db
        .prepare('SELECT * FROM orders WHERE UPPER(TRIM(order_number)) = ? ORDER BY id DESC')
        .all(rawQuery.toUpperCase()) as any[];
      if (byOrderNo.length > 0) {
        matchingOrders = byOrderNo;
      } else {
        const patterns = buildPhonePatterns(rawQuery);
        if (patterns.length > 0) {
          const placeholders = patterns.map(() => `${phoneNormalizedSql} = ?`).join(' OR ');
          matchingOrders = db
            .prepare(`SELECT * FROM orders WHERE (${placeholders}) ORDER BY id DESC LIMIT 20`)
            .all(...patterns) as any[];
        }
      }
    }
  }

  if (!matchingOrders || matchingOrders.length === 0) {
    res.status(404).json({ error: 'Không tìm thấy đơn hàng phù hợp với thông tin đã nhập.' });
    return;
  }

  const enriched = matchingOrders.map((o) => ({
    ...o,
    shipping_tracking: buildLiveShippingTracking(o),
    items: db
      .prepare(
        "SELECT oi.*, p.image_key as product_image_key, p.slug as product_slug, p.category as product_category, CASE WHEN p.category = 'roasted_beans' OR (p.pricing_tiers_json IS NOT NULL AND p.pricing_tiers_json != '[]' AND p.pricing_tiers_json != '') THEN 'kg' ELSE 'unit' END as unit FROM order_items oi LEFT JOIN products p ON oi.product_id = p.id WHERE oi.order_id = ?"
      )
      .all(o.id),
    gift_dispatches: maskGiftDispatches(
      db.prepare('SELECT * FROM gift_voucher_dispatches WHERE order_id = ? ORDER BY id ASC').all(o.id) as any[]
    ),
  }));

  res.json({ orders: enriched, order: enriched[0] });
});

app.get('/api/orders/shipping-status', (req, res) => {
  const rawOrderId = String(req.query.orderId || req.query.orderNumber || '').trim().toUpperCase();
  const rawEmail = String(req.query.email || '').trim().toLowerCase();

  if (!rawOrderId || !rawEmail) {
    res.status(400).json({ error: 'Vui lòng nhập đầy đủ Mã đơn hàng (Order ID) và Email đặt hàng.' });
    return;
  }

  const order = db
    .prepare('SELECT * FROM orders WHERE UPPER(TRIM(order_number)) = ? AND LOWER(TRIM(customer_email)) = ? ORDER BY id DESC LIMIT 1')
    .get(rawOrderId, rawEmail) as any;

  if (!order) {
    res.status(404).json({ error: 'Không tìm thấy đơn hàng khớp với Mã đơn hàng và Email đã nhập.' });
    return;
  }

  const items = db
    .prepare(
      "SELECT oi.*, p.image_key as product_image_key, p.slug as product_slug, p.category as product_category, CASE WHEN p.category = 'roasted_beans' OR (p.pricing_tiers_json IS NOT NULL AND p.pricing_tiers_json != '[]' AND p.pricing_tiers_json != '') THEN 'kg' ELSE 'unit' END as unit FROM order_items oi LEFT JOIN products p ON oi.product_id = p.id WHERE oi.order_id = ?"
    )
    .all(order.id);

  const shipping = buildLiveShippingTracking(order);
  res.json({
    ok: true,
    shipping,
    order: {
      ...order,
      shipping_tracking: shipping,
      items,
    },
  });
});

app.post('/api/orders/:orderNumber/request-action', requireAuth, (req: AuthedRequest, res) => {
  const { action } = req.body || {};
  const order = db
    .prepare('SELECT * FROM orders WHERE order_number = ? AND user_id = ?')
    .get(req.params.orderNumber, req.authUser!.userId) as any;
  if (!order) {
    res.status(404).json({ error: 'Order not found' });
    return;
  }
  if (action === 'cancel' && (order.order_status === 'Pending' || order.order_status === 'Confirmed')) {
    db.prepare("UPDATE orders SET order_status = 'Cancelled', updated_at = datetime('now') WHERE id = ?").run(order.id);
    db.prepare("DELETE FROM points_ledger WHERE order_id = ? AND entry_type = 'earn_pending'").run(order.id);
    res.json({ ok: true, status: 'Cancelled' });
    return;
  }
  if (action === 'return' && order.order_status === 'Completed') {
    db.prepare("UPDATE orders SET notes = notes || ' [Return Requested]', updated_at = datetime('now') WHERE id = ?").run(order.id);
    res.json({ ok: true, status: 'Return Requested' });
    return;
  }
  res.status(400).json({ error: 'Action not allowed for current order status' });
});

// ---------- B2B / OEM / EXPORT / CONTACT / NEWSLETTER ----------
app.post('/api/b2b/inquiries', (req, res) => {
  const {
    inquiryType,
    companyName = '',
    contactName,
    email,
    phone,
    country = 'Vietnam',
    businessType = '',
    productSku = '',
    packagingOption = '',
    estimatedVolume = '',
    message,
  } = req.body || {};

  if (!inquiryType || !contactName || !email || !phone || !message) {
    res.status(400).json({ error: 'Please complete all required inquiry fields' });
    return;
  }
  const validTypes = [
    'sample_request',
    'green_quotation',
    'wholesale_partner',
    'horeca',
    'oem_private_label',
    'export_inquiry',
    'corporate_gifting',
    'contact',
  ];
  if (!validTypes.includes(inquiryType)) {
    res.status(400).json({ error: 'Invalid inquiry type' });
    return;
  }

  const result = db
    .prepare(`
      INSERT INTO b2b_inquiries (
        inquiry_type, company_name, contact_name, email, phone, country,
        business_type, product_sku, packaging_option, estimated_volume, message
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `)
    .run(
      inquiryType,
      String(companyName).trim(),
      String(contactName).trim(),
      String(email).trim().toLowerCase(),
      String(phone).trim(),
      String(country).trim(),
      String(businessType).trim(),
      String(productSku).trim(),
      String(packagingOption).trim(),
      String(estimatedVolume).trim(),
      String(message).trim()
    );

  const inquiryId = Number(result.lastInsertRowid);
  dispatchB2BInquiryEmail({
    inquiryId,
    inquiryType,
    companyName: String(companyName).trim(),
    contactName: String(contactName).trim(),
    email: String(email).trim().toLowerCase(),
    phone: String(phone).trim(),
    productSku: String(productSku).trim(),
    estimatedVolume: String(estimatedVolume).trim(),
    message: String(message).trim(),
  });
  res.status(201).json({ ok: true, inquiryId });
});

app.post('/api/newsletter', (req, res) => {
  const { email, lang = 'vi' } = req.body || {};
  if (!email || !String(email).includes('@')) {
    res.status(400).json({ error: 'Valid email address is required' });
    return;
  }
  const normalized = String(email).trim().toLowerCase();
  db.prepare('INSERT OR IGNORE INTO newsletter_subscribers (email, lang) VALUES (?, ?)').run(normalized, lang === 'en' ? 'en' : 'vi');
  res.status(201).json({ ok: true });
});

// ---------- JOURNAL ----------
app.get('/api/journal', (req, res) => {
  const { category, search } = req.query;
  let sql = 'SELECT * FROM journal_articles WHERE published = 1';
  const params: any[] = [];
  if (category && category !== 'all') {
    sql += ' AND category = ?';
    params.push(category);
  }
  if (search) {
    const q = `%${String(search).trim().toLowerCase()}%`;
    sql += ' AND (LOWER(title_vi) LIKE ? OR LOWER(title_en) LIKE ? OR LOWER(excerpt_vi) LIKE ? OR LOWER(excerpt_en) LIKE ?)';
    params.push(q, q, q, q);
  }
  sql += ' ORDER BY published_at DESC, id DESC';
  const articles = db.prepare(sql).all(...params).map((a: any) => ({
    ...a,
    tags: JSON.parse(a.tags_json || '[]'),
  }));
  res.json({ articles });
});

app.get('/api/journal/:slug', (req, res) => {
  const article = db.prepare('SELECT * FROM journal_articles WHERE slug = ? AND published = 1').get(req.params.slug) as any;
  if (!article) {
    res.status(404).json({ error: 'Article not found' });
    return;
  }
  const related = db
    .prepare(
      'SELECT * FROM journal_articles WHERE id != ? AND published = 1 ORDER BY CASE WHEN category = ? THEN 0 ELSE 1 END, published_at DESC, id DESC LIMIT 3'
    )
    .all(article.id, article.category);
  res.json({
    article: { ...article, tags: JSON.parse(article.tags_json || '[]') },
    related,
  });
});

// ---------- PROTECTED ADMIN CMS ROUTES ----------
app.get('/api/admin/overview', requirePermission('overview'), (_req, res) => {
  const revRow = db
    .prepare("SELECT COALESCE(SUM(total), 0) as revenue, COUNT(*) as totalOrders, COALESCE(AVG(total), 0) as aov FROM orders WHERE order_status != 'Cancelled'")
    .get() as { revenue: number; totalOrders: number; aov: number };
  const memberCount = (db.prepare("SELECT COUNT(*) as c FROM users WHERE role = 'customer'").get() as { c: number }).c;
  const b2bCount = (db.prepare('SELECT COUNT(*) as c FROM b2b_inquiries').get() as { c: number }).c;
  const productCount = (db.prepare('SELECT COUNT(*) as c FROM products').get() as { c: number }).c;
  const articleCount = (db.prepare('SELECT COUNT(*) as c FROM journal_articles').get() as { c: number }).c;
  const mediaCount = (db.prepare('SELECT COUNT(*) as c FROM media_assets').get() as { c: number }).c;
  const issuedPts = (db.prepare("SELECT COALESCE(SUM(points), 0) as s FROM points_ledger WHERE entry_type IN ('earn_available','admin_adjustment') AND points > 0").get() as { s: number }).s;
  const redeemedPts = (db.prepare("SELECT COALESCE(SUM(ABS(points)), 0) as s FROM points_ledger WHERE entry_type = 'redeem'").get() as { s: number }).s;
  const productPerf = db
    .prepare(`
      SELECT sku, product_name_vi, product_name_en, SUM(quantity) as units_sold, SUM(line_total_vnd) as revenue
      FROM order_items
      GROUP BY sku, product_name_vi, product_name_en
      ORDER BY revenue DESC
      LIMIT 8
    `)
    .all();
  const auditLogs = db.prepare('SELECT * FROM audit_logs ORDER BY id DESC LIMIT 40').all();

  res.json({
    metrics: {
      revenue: revRow.revenue,
      totalOrders: revRow.totalOrders,
      avgOrderValue: Math.round(revRow.aov),
      members: memberCount,
      b2bInquiries: b2bCount,
      products: productCount,
      articles: articleCount,
      mediaAssets: mediaCount,
      pointsIssued: issuedPts,
      pointsRedeemed: redeemedPts,
    },
    productPerformance: productPerf,
    auditLogs,
  });
});

function toSafeSlug(raw: string): string {
  return String(raw || '')
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g, '')
    .replace(/đ/g, 'd')
    .replace(/Đ/g, 'd')
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '');
}

app.get('/api/admin/products', requirePermission('products'), (_req, res) => {
  const rows = db.prepare('SELECT * FROM products ORDER BY category ASC, id DESC').all() as any[];
  const products = rows.map((p) => ({
    ...p,
    barcode: p.barcode || '',
    brewing_methods: JSON.parse(p.brewing_methods_json || '[]'),
    variants: JSON.parse(p.variants_json || '[]'),
    pricing_tiers: JSON.parse(p.pricing_tiers_json || '[]'),
    packaging_options: JSON.parse(p.packaging_options_json || '[]'),
    gallery_images: JSON.parse(p.gallery_images_json || '[]'),
  }));
  res.json({ products });
});

app.post('/api/admin/products', requirePermission('products'), async (req: AuthedRequest, res) => {
  const b = req.body || {};
  if (!b.sku || !b.name_vi || !b.category) {
    res.status(400).json({ error: 'Vui lòng nhập Mã SKU, Tên sản phẩm và Danh mục.' });
    return;
  }
  const slug = toSafeSlug(b.slug || b.name_vi || b.sku) || `sp-${Date.now()}`;
  const existingSlug = db.prepare('SELECT id FROM products WHERE slug = ? OR sku = ?').get(slug, String(b.sku).trim());
  if (existingSlug) {
    res.status(409).json({ error: 'Mã SKU hoặc đường dẫn (slug) đã tồn tại.' });
    return;
  }
  const vcb = await getVietcombankUsdRate(db);
  const pricingTiers = Array.isArray(b.pricing_tiers) ? normalizeVolumeTiers(b.pricing_tiers, vcb.activeRate) : [];
  const effectivePriceVnd =
    pricingTiers.length > 0 && (b.category === 'roasted_beans' || !Number(b.price_vnd))
      ? pricingTiers[0].priceVnd
      : Number(b.price_vnd || 0);
  const effectivePriceUsd =
    Number(b.price_usd) > 0
      ? Number(b.price_usd)
      : pricingTiers.length > 0
        ? pricingTiers[0].priceUsd
        : convertVndToUsdByRate(effectivePriceVnd, vcb.activeRate);
  const effectiveVariants =
    pricingTiers.length > 0 && b.category === 'roasted_beans'
      ? pricingTiers.map((t) => ({ label: t.labelVi, priceVnd: t.priceVnd, priceUsd: t.priceUsd }))
      : Array.isArray(b.variants)
        ? b.variants
        : [];
  const effectiveBarcode = String(b.barcode || '').trim() || generateEan13Barcode(`${b.sku}-${Date.now()}`);

  const result = db
    .prepare(`
      INSERT INTO products (
        slug, sku, barcode, category, sub_category, name_vi, name_en, subtitle_vi, subtitle_en,
        description_vi, description_en, coffee_type, blend_summary_vi, blend_summary_en, blend_public,
        roast_profile_vi, roast_profile_en, tasting_notes_vi, tasting_notes_en,
        brewing_methods_json, variants_json, pricing_tiers_json, packaging_options_json,
        price_vnd, price_usd, inventory, moq, status, is_demo_data,
        mascot_slug, screen_size, processing_method, origin_region,
        harvest_year, moisture_content, density, defect_info, grading_spec, image_key, gallery_images_json, featured
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `)
    .run(
      slug,
      String(b.sku).trim(),
      effectiveBarcode,
      b.category,
      b.sub_category || '',
      String(b.name_vi).trim(),
      String(b.name_en || b.name_vi).trim(),
      b.subtitle_vi || '',
      b.subtitle_en || b.subtitle_vi || '',
      b.description_vi || '',
      b.description_en || b.description_vi || '',
      b.coffee_type || '',
      b.blend_summary_vi || '',
      b.blend_summary_en || '',
      b.blend_public ? 1 : 0,
      b.roast_profile_vi || '',
      b.roast_profile_en || '',
      b.tasting_notes_vi || '',
      b.tasting_notes_en || b.tasting_notes_vi || '',
      JSON.stringify(Array.isArray(b.brewing_methods) ? b.brewing_methods : []),
      JSON.stringify(effectiveVariants),
      JSON.stringify(pricingTiers),
      JSON.stringify(Array.isArray(b.packaging_options) ? b.packaging_options : []),
      effectivePriceVnd,
      effectivePriceUsd,
      Number(b.inventory || 0),
      b.moq || (b.category === 'roasted_beans' ? '1 kg' : '1'),
      b.status || 'active',
      b.is_demo_data ? 1 : 0,
      b.mascot_slug || '',
      b.screen_size || '',
      b.processing_method || '',
      b.origin_region || '',
      b.harvest_year || 'Đang cập nhật vụ mùa',
      b.moisture_content || 'Đang chờ phiếu kiểm nghiệm COA',
      b.density || 'Đang chờ phiếu kiểm nghiệm COA',
      b.defect_info || 'Đang chờ phiếu kiểm nghiệm COA',
      b.grading_spec || '',
      b.image_key || 'product_robusta_house',
      JSON.stringify(Array.isArray(b.gallery_images) ? b.gallery_images : []),
      b.featured ? 1 : 0
    );

  logAudit(req.authUser!.userId, req.authUser!.email, 'CREATE_PRODUCT', 'product', Number(result.lastInsertRowid), { sku: b.sku, barcode: effectiveBarcode });
  scheduleSnapshotSync(db);
  res.status(201).json({ ok: true, id: Number(result.lastInsertRowid), barcode: effectiveBarcode });
});

app.patch('/api/admin/products/:id', requirePermission('products'), async (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const existing = db.prepare('SELECT * FROM products WHERE id = ?').get(id) as any;
  if (!existing) {
    res.status(404).json({ error: 'Không tìm thấy sản phẩm' });
    return;
  }
  const b = req.body || {};
  const nextSlug = b.slug ? toSafeSlug(b.slug) || existing.slug : existing.slug;
  const vcb = await getVietcombankUsdRate(db);

  const nextCategory = b.category ?? existing.category;
  const nextPricingTiers =
    b.pricing_tiers !== undefined
      ? normalizeVolumeTiers(b.pricing_tiers, vcb.activeRate)
      : JSON.parse(existing.pricing_tiers_json || '[]');

  let resolvedPriceVnd = b.price_vnd !== undefined ? Number(b.price_vnd) : existing.price_vnd;
  let resolvedPriceUsd = b.price_usd !== undefined ? Number(b.price_usd) : existing.price_usd;

  if (nextCategory === 'roasted_beans' && nextPricingTiers.length > 0 && b.pricing_tiers !== undefined) {
    resolvedPriceVnd = nextPricingTiers[0].priceVnd;
    resolvedPriceUsd = nextPricingTiers[0].priceUsd;
  } else if (b.price_vnd !== undefined && b.price_usd === undefined) {
    resolvedPriceUsd = convertVndToUsdByRate(Number(b.price_vnd), vcb.activeRate);
  }

  const nextVariantsJson =
    b.pricing_tiers !== undefined && nextCategory === 'roasted_beans' && nextPricingTiers.length > 0
      ? JSON.stringify(nextPricingTiers.map((t: any) => ({ label: t.labelVi, priceVnd: t.priceVnd, priceUsd: t.priceUsd })))
      : b.variants !== undefined
        ? JSON.stringify(b.variants)
        : existing.variants_json;

  const nextBarcode = b.barcode !== undefined ? String(b.barcode).trim() : existing.barcode || '';

  db.prepare(`
    UPDATE products SET
      sku = ?, barcode = ?, slug = ?, category = ?, sub_category = ?,
      name_vi = ?, name_en = ?, subtitle_vi = ?, subtitle_en = ?,
      description_vi = ?, description_en = ?, coffee_type = ?,
      blend_summary_vi = ?, blend_summary_en = ?, blend_public = ?,
      roast_profile_vi = ?, roast_profile_en = ?,
      tasting_notes_vi = ?, tasting_notes_en = ?,
      brewing_methods_json = ?, variants_json = ?, pricing_tiers_json = ?, packaging_options_json = ?,
      price_vnd = ?, price_usd = ?, inventory = ?, moq = ?, status = ?,
      mascot_slug = ?, screen_size = ?, processing_method = ?, origin_region = ?,
      harvest_year = ?, moisture_content = ?, density = ?, defect_info = ?,
      grading_spec = ?, image_key = ?, gallery_images_json = ?, featured = ?
    WHERE id = ?
  `).run(
    b.sku ?? existing.sku,
    nextBarcode,
    nextSlug,
    nextCategory,
    b.sub_category ?? existing.sub_category,
    b.name_vi ?? existing.name_vi,
    b.name_en ?? existing.name_en,
    b.subtitle_vi ?? existing.subtitle_vi,
    b.subtitle_en ?? existing.subtitle_en,
    b.description_vi ?? existing.description_vi,
    b.description_en ?? existing.description_en,
    b.coffee_type ?? existing.coffee_type,
    b.blend_summary_vi ?? existing.blend_summary_vi,
    b.blend_summary_en ?? existing.blend_summary_en,
    b.blend_public !== undefined ? (b.blend_public ? 1 : 0) : existing.blend_public,
    b.roast_profile_vi ?? existing.roast_profile_vi,
    b.roast_profile_en ?? existing.roast_profile_en,
    b.tasting_notes_vi ?? existing.tasting_notes_vi,
    b.tasting_notes_en ?? existing.tasting_notes_en,
    b.brewing_methods !== undefined ? JSON.stringify(b.brewing_methods) : existing.brewing_methods_json,
    nextVariantsJson,
    b.pricing_tiers !== undefined ? JSON.stringify(nextPricingTiers) : existing.pricing_tiers_json,
    b.packaging_options !== undefined ? JSON.stringify(b.packaging_options) : existing.packaging_options_json,
    resolvedPriceVnd,
    resolvedPriceUsd,
    b.inventory !== undefined ? Number(b.inventory) : existing.inventory,
    b.moq ?? existing.moq,
    b.status ?? existing.status,
    b.mascot_slug ?? existing.mascot_slug,
    b.screen_size ?? existing.screen_size,
    b.processing_method ?? existing.processing_method,
    b.origin_region ?? existing.origin_region,
    b.harvest_year ?? existing.harvest_year,
    b.moisture_content ?? existing.moisture_content,
    b.density ?? existing.density,
    b.defect_info ?? existing.defect_info,
    b.grading_spec ?? existing.grading_spec,
    b.image_key ?? existing.image_key,
    b.gallery_images !== undefined ? JSON.stringify(b.gallery_images) : existing.gallery_images_json,
    b.featured !== undefined ? (b.featured ? 1 : 0) : existing.featured,
    id
  );
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_PRODUCT', 'product', id, { sku: b.sku ?? existing.sku, barcode: nextBarcode });
  scheduleSnapshotSync(db);
  res.json({ ok: true, price_usd: resolvedPriceUsd, barcode: nextBarcode });
});

app.delete('/api/admin/products/:id', requirePermission('products'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const existing = db.prepare('SELECT * FROM products WHERE id = ?').get(id) as any;
  if (!existing) {
    res.status(404).json({ error: 'Không tìm thấy sản phẩm' });
    return;
  }
  const refs = (db.prepare('SELECT COUNT(*) as c FROM order_items WHERE product_id = ?').get(id) as { c: number }).c;
  if (refs > 0 && req.query.archive !== 'true') {
    res.status(409).json({
      error: 'Sản phẩm đã phát sinh trong đơn hàng. Hãy chọn Lưu trữ (ẩn khỏi cửa hàng) thay vì xóa vĩnh viễn.',
      canArchive: true,
    });
    return;
  }
  if (refs > 0 && req.query.archive === 'true') {
    db.prepare("UPDATE products SET status = 'draft' WHERE id = ?").run(id);
    logAudit(req.authUser!.userId, req.authUser!.email, 'ARCHIVE_PRODUCT', 'product', id, { sku: existing.sku });
    scheduleSnapshotSync(db);
    res.json({ ok: true, archived: true });
    return;
  }
  db.prepare('DELETE FROM product_reviews WHERE product_id = ?').run(id);
  db.prepare('DELETE FROM products WHERE id = ?').run(id);
  logAudit(req.authUser!.userId, req.authUser!.email, 'DELETE_PRODUCT', 'product', id, { sku: existing.sku });
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

app.get('/api/admin/orders', requirePermission('orders'), (_req, res) => {
  const orders = db.prepare('SELECT * FROM orders ORDER BY id DESC').all() as any[];
  const enriched = orders.map((o) => ({
    ...o,
    items: db
      .prepare(
        "SELECT oi.*, p.image_key as product_image_key, p.slug as product_slug, p.category as product_category, CASE WHEN p.category = 'roasted_beans' OR (p.pricing_tiers_json IS NOT NULL AND p.pricing_tiers_json != '[]' AND p.pricing_tiers_json != '') THEN 'kg' ELSE 'unit' END as unit FROM order_items oi LEFT JOIN products p ON oi.product_id = p.id WHERE oi.order_id = ?"
      )
      .all(o.id),
  }));
  res.json({ orders: enriched });
});

app.patch('/api/admin/orders/:id', requirePermission('orders'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const { orderStatus, paymentStatus, trackingCode, resolutionNote } = req.body || {};
  const order = db.prepare('SELECT * FROM orders WHERE id = ?').get(id) as any;
  if (!order) {
    res.status(404).json({ error: 'Order not found' });
    return;
  }

  const updateTx = db.transaction(() => {
    const prevStatus = order.order_status;
    const nextStatus = orderStatus || prevStatus;
    const nextPayment = paymentStatus || order.payment_status;
    const nextTracking = trackingCode !== undefined ? String(trackingCode).trim() : order.tracking_code;
    const cleanResolution = typeof resolutionNote === 'string' ? resolutionNote.trim() : '';
    const nextNotes = cleanResolution
      ? `${order.notes ? `${order.notes}\n` : ''}[Xử lý ${new Date().toISOString().slice(0, 16).replace('T', ' ')}] ${cleanResolution}`
      : order.notes;

    db.prepare(`
      UPDATE orders SET order_status = ?, payment_status = ?, tracking_code = ?, notes = ?, updated_at = datetime('now') WHERE id = ?
    `).run(nextStatus, nextPayment, nextTracking, nextNotes, id);

    // Activate any digital Gift Vouchers tied to this order once payment is reconciled
    if (nextPayment === 'paid' && nextStatus !== 'Cancelled' && nextStatus !== 'Returned') {
      db.prepare("UPDATE gift_voucher_dispatches SET status = 'active' WHERE order_id = ? AND status = 'pending_payment'").run(id);
    }

    // Restock inventory when cancelling or returning from an active order state
    if (
      prevStatus !== nextStatus &&
      prevStatus !== 'Cancelled' &&
      prevStatus !== 'Returned' &&
      (nextStatus === 'Cancelled' || nextStatus === 'Returned')
    ) {
      const orderItems = db.prepare('SELECT product_id, quantity FROM order_items WHERE order_id = ?').all(id) as Array<{
        product_id: number;
        quantity: number;
      }>;
      for (const item of orderItems) {
        db.prepare('UPDATE products SET inventory = inventory + ? WHERE id = ?').run(item.quantity, item.product_id);
      }
      db.prepare("DELETE FROM points_ledger WHERE order_id = ? AND entry_type = 'earn_pending'").run(order.id);
      db.prepare("UPDATE gift_voucher_dispatches SET status = 'cancelled' WHERE order_id = ? AND status IN ('pending_payment', 'active')").run(id);
    }

    // Server-side loyalty points settlement: credit on Completed (prevent duplicate credits!), reverse on Cancelled/Returned
    if (order.user_id && nextStatus === 'Completed' && !order.points_awarded) {
      const loyalty = db.prepare('SELECT * FROM loyalty_settings WHERE id = 1').get() as any;
      const syncedBuyerTier = syncUserTierInDb(order.user_id);
      const tier = db.prepare('SELECT point_multiplier FROM membership_tiers WHERE name = ?').get(syncedBuyerTier) as { point_multiplier: number } | undefined;
      const netEligible = Math.max(0, order.subtotal - order.discount_amount - order.points_discount);
      const pts = Math.floor((netEligible / 10000) * (loyalty?.points_per_10k_vnd || 1) * (tier?.point_multiplier || 1));

      db.prepare("DELETE FROM points_ledger WHERE order_id = ? AND entry_type = 'earn_pending'").run(order.id);
      if (pts > 0) {
        db.prepare(`
          INSERT INTO points_ledger (user_id, order_id, entry_type, points, description_vi, description_en, expires_at)
          VALUES (?, ?, 'earn_available', ?, ?, ?, datetime('now', '+${loyalty?.expiration_days || 365} days'))
        `).run(
          order.user_id,
          order.id,
          pts,
          `Tích điểm hoàn tất đơn hàng ${order.order_number}`,
          `Earned points from completed order ${order.order_number}`
        );
      }
      db.prepare('UPDATE orders SET points_awarded = ? WHERE id = ?').run(pts, order.id);
    }

    if (order.user_id && (nextStatus === 'Cancelled' || nextStatus === 'Returned') && order.points_awarded > 0) {
      const alreadyReversed = db.prepare("SELECT id FROM points_ledger WHERE order_id = ? AND entry_type = 'reverse'").get(order.id);
      if (!alreadyReversed) {
        db.prepare(`
          INSERT INTO points_ledger (user_id, order_id, entry_type, points, description_vi, description_en)
          VALUES (?, ?, 'reverse', ?, ?, ?)
        `).run(
          order.user_id,
          order.id,
          -order.points_awarded,
          `Hoàn trừ điểm do đơn hàng ${order.order_number} bị ${nextStatus}`,
          `Reversed points for ${nextStatus.toLowerCase()} order ${order.order_number}`
        );
      }
    }

    // Automatically push bilingual notification to customer when order status or resolution changes
    if (order.user_id && (prevStatus !== nextStatus || cleanResolution || (nextPayment === 'paid' && order.payment_status !== 'paid'))) {
      const statusCopy: Record<string, { vi: string; en: string; msgVi: string; msgEn: string }> = {
        Confirmed: {
          vi: `Đơn hàng ${order.order_number} đã được duyệt`,
          en: `Order ${order.order_number} confirmed`,
          msgVi: 'ROAR COFFEE đã duyệt đơn hàng của bạn và chuyển sang bộ phận rang đóng gói.',
          msgEn: 'Your order has been approved and queued for fresh batch packaging.',
        },
        Processing: {
          vi: `Đơn ${order.order_number} đang được đóng gói`,
          en: `Packing order ${order.order_number}`,
          msgVi: 'Xưởng rang đang niêm phong túi van một chiều và bàn giao cho đơn vị vận chuyển.',
          msgEn: 'Our roastery team is packing your bags and preparing courier dispatch.',
        },
        Shipping: {
          vi: `Đơn ${order.order_number} đang trên đường giao`,
          en: `Order ${order.order_number} is out for delivery`,
          msgVi: nextTracking
            ? `Đơn hàng đã bàn giao cho đơn vị vận chuyển. Mã vận đơn: ${nextTracking}.`
            : 'Đơn hàng đã được giao cho đơn vị vận chuyển.',
          msgEn: nextTracking
            ? `Shipped via carrier with tracking code ${nextTracking}.`
            : 'Your order has been handed to the delivery carrier.',
        },
        Completed: {
          vi: `Hoàn tất đơn hàng ${order.order_number}`,
          en: `Order ${order.order_number} delivered & completed`,
          msgVi: 'Cảm ơn bạn đã thưởng thức ROAR COFFEE! Điểm thưởng thành viên đã được cộng vào ví điểm.',
          msgEn: 'Thank you for brewing with ROAR COFFEE! Your loyalty points have been settled.',
        },
        Cancelled: {
          vi: `Đơn hàng ${order.order_number} đã hủy`,
          en: `Order ${order.order_number} cancelled`,
          msgVi: cleanResolution || 'Đơn hàng đã được hủy theo yêu cầu hoặc xử lý hoàn tất từ bộ phận CSKH.',
          msgEn: cleanResolution || 'This order has been cancelled and inventory released.',
        },
        Returned: {
          vi: `Đã giải quyết trả hàng / hoàn tiền đơn ${order.order_number}`,
          en: `Return / refund resolved for ${order.order_number}`,
          msgVi: cleanResolution || 'Yêu cầu trả hàng / hoàn tiền của bạn đã được xử lý.',
          msgEn: cleanResolution || 'Your return / refund resolution has been completed.',
        },
      };

      const mapped = statusCopy[nextStatus];
      if (mapped) {
        createUserNotification(order.user_id, {
          titleVi: mapped.vi,
          titleEn: mapped.en,
          messageVi: cleanResolution && nextStatus !== 'Cancelled' && nextStatus !== 'Returned' ? `${mapped.msgVi} (${cleanResolution})` : mapped.msgVi,
          messageEn: cleanResolution && nextStatus !== 'Cancelled' && nextStatus !== 'Returned' ? `${mapped.msgEn} (${cleanResolution})` : mapped.msgEn,
          category: 'order',
          linkUrl: '/account?tab=orders',
        });
      } else if (nextPayment === 'paid' && order.payment_status !== 'paid') {
        createUserNotification(order.user_id, {
          titleVi: `Xác nhận thanh toán đơn ${order.order_number}`,
          titleEn: `Payment confirmed for ${order.order_number}`,
          messageVi: 'Bộ phận kế toán đã xác nhận thanh toán thành công cho đơn hàng của bạn.',
          messageEn: 'Payment reconciliation succeeded for your order.',
          category: 'order',
          linkUrl: '/account?tab=orders',
        });
      }
    }
  });

  updateTx();
  if (order.user_id) {
    syncUserTierInDb(order.user_id);
  }
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_ORDER', 'order', id, {
    orderStatus,
    paymentStatus,
    trackingCode,
    resolutionNote,
  });
  res.json({ ok: true });
});

app.get('/api/admin/customers', requirePermission('customers'), (_req, res) => {
  syncUnlinkedOrderCustomers();
  const users = db
    .prepare('SELECT id, email, full_name, phone, role, admin_role, member_code, tier, wallet_balance_vnd, email_verified, company_name, b2b_verified, deletion_requested, created_at, password_hash FROM users ORDER BY id DESC')
    .all() as any[];
  const enriched = users.map((u) => {
    const syncedTier = syncUserTierInDb(u.id);
    const orderStats = db
      .prepare("SELECT COUNT(*) as c, COALESCE(SUM(total), 0) as spent FROM orders WHERE (user_id = ? OR LOWER(TRIM(customer_email)) = LOWER(TRIM(?))) AND order_status != 'Cancelled'")
      .get(u.id, u.email || '') as { c: number; spent: number };
    const unreadNotifications = (
      db.prepare('SELECT COUNT(*) as c FROM user_notifications WHERE user_id = ? AND is_read = 0').get(u.id) as { c: number }
    ).c;
    const { password_hash: rawHash, ...safeUser } = u;
    return {
      ...safeUser,
      has_password: Boolean(rawHash && String(rawHash).includes(':')),
      tier: syncedTier,
      points: getPointsSummary(u.id),
      orderCount: orderStats.c,
      totalSpent: orderStats.spent,
      unreadNotifications,
    };
  });
  const tiers = db.prepare('SELECT * FROM membership_tiers ORDER BY min_spend_vnd ASC').all();
  const loyaltySettings = db.prepare('SELECT * FROM loyalty_settings WHERE id = 1').get();
  res.json({ customers: enriched, tiers, loyaltySettings });
});

app.patch('/api/admin/customers/:id', requirePermission('customers'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const { tier, b2bVerified, pointsDelta, adjustmentNote } = req.body || {};
  const user = db.prepare('SELECT * FROM users WHERE id = ?').get(id) as any;
  if (!user) {
    res.status(404).json({ error: 'User not found' });
    return;
  }
  const normalizedTier = tier ? normalizeMembershipTierName(String(tier)) : null;
  if (normalizedTier) db.prepare('UPDATE users SET tier = ? WHERE id = ?').run(normalizedTier, id);
  if (b2bVerified !== undefined) db.prepare('UPDATE users SET b2b_verified = ? WHERE id = ?').run(b2bVerified ? 1 : 0, id);
  if (pointsDelta && Number(pointsDelta) !== 0) {
    const delta = Math.trunc(Number(pointsDelta));
    db.prepare(`
      INSERT INTO points_ledger (user_id, entry_type, points, description_vi, description_en)
      VALUES (?, 'admin_adjustment', ?, ?, ?)
    `).run(id, delta, adjustmentNote || 'Điều chỉnh điểm bởi Quản trị viên', adjustmentNote || 'Administrator adjustment');
    createUserNotification(id, {
      titleVi: delta > 0 ? `Bạn nhận được +${delta} điểm thưởng ROAR` : `Điều chỉnh ${delta} điểm thưởng ROAR`,
      titleEn: delta > 0 ? `You received +${delta} ROAR bonus points` : `ROAR points adjustment (${delta})`,
      messageVi: adjustmentNote || 'Quản trị viên ROAR COFFEE vừa cập nhật quỹ điểm thành viên của bạn.',
      messageEn: adjustmentNote || 'A ROAR COFFEE administrator updated your loyalty point balance.',
      category: 'loyalty',
      linkUrl: '/account?tab=rewards',
    });
    if (delta > 0) {
      syncUserTierInDb(id);
    }
  }
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_CUSTOMER', 'user', id, { tier: normalizedTier || tier, pointsDelta });
  res.json({ ok: true });
});

app.post('/api/admin/customers/:id/notify', requirePermission('customers'), (req: AuthedRequest, res) => {
  const targetParam = req.params.id;
  const { titleVi, titleEn, messageVi, messageEn, category = 'promo', linkUrl = '/account?tab=vouchers' } = req.body || {};
  if (!titleVi || !messageVi) {
    res.status(400).json({ error: 'Vui lòng nhập tiêu đề và nội dung thông báo.' });
    return;
  }

  let sentCount = 0;
  if (targetParam === 'all') {
    const customers = db.prepare("SELECT id FROM users WHERE role != 'admin'").all() as Array<{ id: number }>;
    for (const c of customers) {
      createUserNotification(c.id, {
        titleVi: String(titleVi).trim(),
        titleEn: String(titleEn || titleVi).trim(),
        messageVi: String(messageVi).trim(),
        messageEn: String(messageEn || messageVi).trim(),
        category: ['order', 'promo', 'loyalty', 'system'].includes(category) ? category : 'promo',
        linkUrl,
      });
      sentCount += 1;
    }
  } else {
    const uid = Number(targetParam);
    const user = db.prepare('SELECT id FROM users WHERE id = ?').get(uid);
    if (!user) {
      res.status(404).json({ error: 'Không tìm thấy khách hàng' });
      return;
    }
    createUserNotification(uid, {
      titleVi: String(titleVi).trim(),
      titleEn: String(titleEn || titleVi).trim(),
      messageVi: String(messageVi).trim(),
      messageEn: String(messageEn || messageVi).trim(),
      category: ['order', 'promo', 'loyalty', 'system'].includes(category) ? category : 'promo',
      linkUrl,
    });
    sentCount = 1;
  }

  logAudit(req.authUser!.userId, req.authUser!.email, 'SEND_CUSTOMER_NOTIFICATION', 'user_notifications', targetParam, { sentCount });
  res.status(201).json({ ok: true, sentCount });
});

app.patch('/api/admin/loyalty-settings', requirePermission('customers'), (req: AuthedRequest, res) => {
  const { pointsPer10kVnd, vndPerPoint, expirationDays, maxRedeemPercent } = req.body || {};
  db.prepare(`
    UPDATE loyalty_settings SET points_per_10k_vnd = ?, vnd_per_point = ?, expiration_days = ?, max_redeem_percent = ?, updated_at = datetime('now')
    WHERE id = 1
  `).run(
    Number(pointsPer10kVnd || 1),
    Number(vndPerPoint || 100),
    Number(expirationDays || 365),
    Number(maxRedeemPercent || 30)
  );
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_LOYALTY_POLICY', 'loyalty_settings', 1, req.body);
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

app.get('/api/admin/promotions', requirePermission('promotions'), (_req, res) => {
  res.json({ promotions: db.prepare('SELECT * FROM promotions ORDER BY id DESC').all() });
});

app.post('/api/admin/promotions', requirePermission('promotions'), (req: AuthedRequest, res) => {
  const b = req.body || {};
  if (!b.code || !b.title_vi || !b.title_en || !b.start_date || !b.end_date) {
    res.status(400).json({ error: 'Code, bilingual titles, start_date, and end_date are required' });
    return;
  }
  const cleanCode = String(b.code).trim().toUpperCase();
  const result = db
    .prepare(`
      INSERT INTO promotions (
        code, title_vi, title_en, description_vi, description_en, promo_type, discount_type,
        discount_value, max_discount, min_order_value, eligible_category, start_date, end_date,
        usage_limit, member_only, min_tier, terms_vi, terms_en, active
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1)
    `)
    .run(
      cleanCode,
      b.title_vi,
      b.title_en,
      b.description_vi || '',
      b.description_en || '',
      b.promo_type || 'seasonal',
      b.discount_type || 'percent',
      Number(b.discount_value || 0),
      Number(b.max_discount || 0),
      Number(b.min_order_value || 0),
      b.eligible_category || 'all',
      b.start_date,
      b.end_date,
      Number(b.usage_limit || 500),
      b.member_only ? 1 : 0,
      b.min_tier || '',
      b.terms_vi || '',
      b.terms_en || ''
    );

  if (b.notifyCustomers !== false) {
    const members = db.prepare("SELECT id FROM users WHERE role != 'admin'").all() as Array<{ id: number }>;
    for (const m of members) {
      createUserNotification(m.id, {
        titleVi: `Ưu đãi mới: ${b.title_vi} (${cleanCode})`,
        titleEn: `New offer: ${b.title_en} (${cleanCode})`,
        messageVi: b.description_vi || `Sử dụng mã ${cleanCode} tại giỏ hàng hoặc trang thanh toán trước ${b.end_date}.`,
        messageEn: b.description_en || `Apply code ${cleanCode} at checkout before ${b.end_date}.`,
        category: 'promo',
        linkUrl: '/account?tab=vouchers',
      });
    }
  }

  logAudit(req.authUser!.userId, req.authUser!.email, 'CREATE_PROMOTION', 'promotion', Number(result.lastInsertRowid), { code: cleanCode });
  scheduleSnapshotSync(db);
  res.status(201).json({ ok: true });
});

app.patch('/api/admin/promotions/:id', requirePermission('promotions'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const { active } = req.body || {};
  db.prepare('UPDATE promotions SET active = ? WHERE id = ?').run(active ? 1 : 0, id);
  logAudit(req.authUser!.userId, req.authUser!.email, 'TOGGLE_PROMOTION', 'promotion', id, { active });
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

app.get('/api/admin/b2b', requirePermission('b2b'), (_req, res) => {
  res.json({ inquiries: db.prepare('SELECT * FROM b2b_inquiries ORDER BY id DESC').all() });
});

app.patch('/api/admin/b2b/:id', requirePermission('b2b'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const { status, quotedPrice, adminNotes } = req.body || {};
  db.prepare('UPDATE b2b_inquiries SET status = ?, quoted_price = ?, admin_notes = ? WHERE id = ?').run(
    status || 'reviewing',
    quotedPrice || '',
    adminNotes || '',
    id
  );
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_B2B_INQUIRY', 'b2b_inquiry', id, { status });
  res.json({ ok: true });
});

app.delete('/api/admin/b2b/:id', requirePermission('b2b'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  db.prepare('DELETE FROM b2b_inquiries WHERE id = ?').run(id);
  logAudit(req.authUser!.userId, req.authUser!.email, 'DELETE_B2B_INQUIRY', 'b2b_inquiry', id, {});
  res.json({ ok: true });
});

app.get('/api/admin/newsletter', requirePermission('b2b'), (_req, res) => {
  res.json({ subscribers: db.prepare('SELECT * FROM newsletter_subscribers ORDER BY id DESC').all() });
});

app.delete('/api/admin/newsletter/:id', requirePermission('b2b'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  db.prepare('DELETE FROM newsletter_subscribers WHERE id = ?').run(id);
  logAudit(req.authUser!.userId, req.authUser!.email, 'DELETE_NEWSLETTER_SUBSCRIBER', 'newsletter', id, {});
  res.json({ ok: true });
});

app.patch('/api/admin/personalities/:id', requirePermission('brand'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const { customImageUrl, storyVi, storyEn, traitsVi, traitsEn } = req.body || {};
  const existing = db.prepare('SELECT * FROM personalities WHERE id = ?').get(id) as any;
  if (!existing) {
    res.status(404).json({ error: 'Personality not found' });
    return;
  }
  db.prepare(`
    UPDATE personalities SET custom_image_url = ?, story_vi = ?, story_en = ?, traits_vi = ?, traits_en = ? WHERE id = ?
  `).run(
    customImageUrl ?? existing.custom_image_url,
    storyVi ?? existing.story_vi,
    storyEn ?? existing.story_en,
    traitsVi ?? existing.traits_vi,
    traitsEn ?? existing.traits_en,
    id
  );
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_PERSONALITY', 'personality', id, {});
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

app.patch('/api/admin/origins/:id', requirePermission('brand'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const b = req.body || {};
  const existing = db.prepare('SELECT * FROM coffee_origins WHERE id = ?').get(id) as any;
  if (!existing) {
    res.status(404).json({ error: 'Origin not found' });
    return;
  }
  db.prepare(`
    UPDATE coffee_origins SET sourcing_status = ?, characteristics_vi = ?, characteristics_en = ?, photo_attribution = ? WHERE id = ?
  `).run(
    b.sourcing_status ?? existing.sourcing_status,
    b.characteristics_vi ?? existing.characteristics_vi,
    b.characteristics_en ?? existing.characteristics_en,
    b.photo_attribution ?? existing.photo_attribution,
    id
  );
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_ORIGIN', 'coffee_origin', id, {});
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

// ---------- WORDPRESS-STYLE MEDIA LIBRARY & JOURNAL POSTS & SETTINGS ----------
app.get('/api/admin/media', requirePermission('media', 'posts', 'products', 'pages', 'brand'), (_req, res) => {
  const assets = db.prepare('SELECT * FROM media_assets ORDER BY id DESC').all();
  res.json({ assets });
});

app.post('/api/admin/media', requirePermission('media'), (req: AuthedRequest, res) => {
  const { filename, dataUrl, title = '', altText = '' } = req.body || {};
  if (!filename || !dataUrl || typeof dataUrl !== 'string') {
    res.status(400).json({ error: 'Thiếu tệp hình ảnh hợp lệ.' });
    return;
  }
  const match = /^data:(image\/(?:png|jpeg|jpg|webp|gif));base64,([A-Za-z0-9+/=\s]+)$/i.exec(dataUrl.trim());
  if (!match) {
    res.status(400).json({ error: 'Chỉ hỗ trợ định dạng ảnh PNG, JPG, WEBP hoặc GIF.' });
    return;
  }
  const mimeType = match[1].toLowerCase().replace('image/jpg', 'image/jpeg');
  const extMap: Record<string, string> = {
    'image/png': 'png',
    'image/jpeg': 'jpg',
    'image/webp': 'webp',
    'image/gif': 'gif',
  };
  const ext = extMap[mimeType] || 'png';
  const buffer = Buffer.from(match[2].replace(/\s+/g, ''), 'base64');
  const maxBytes = 6 * 1024 * 1024;
  if (buffer.length === 0 || buffer.length > maxBytes) {
    res.status(400).json({ error: 'Dung lượng ảnh phải lớn hơn 0 và không vượt quá 6MB.' });
    return;
  }

  const baseName = toSafeSlug(String(filename).replace(/\.[^.]+$/, '')) || 'roar-media';
  const storedName = `${Date.now()}-${baseName.slice(0, 48)}.${ext}`;
  const fullPath = path.join(UPLOADS_DIR, storedName);
  fs.writeFileSync(fullPath, buffer);
  const url = `/uploads/${storedName}`;

  const cleanTitle = String(title || baseName).trim();
  const cleanAlt = String(altText || cleanTitle).trim();
  const info = db
    .prepare(`
      INSERT INTO media_assets (filename, url, title, alt_text, mime_type, size_bytes, source_type)
      VALUES (?, ?, ?, ?, ?, ?, 'uploaded')
    `)
    .run(storedName, url, cleanTitle, cleanAlt, mimeType, buffer.length);

  const asset = db.prepare('SELECT * FROM media_assets WHERE id = ?').get(Number(info.lastInsertRowid));
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPLOAD_MEDIA', 'media_asset', Number(info.lastInsertRowid), { url });
  scheduleSnapshotSync(db);
  res.status(201).json({ ok: true, asset });
});

app.patch('/api/admin/media/:id', requirePermission('media'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const existing = db.prepare('SELECT * FROM media_assets WHERE id = ?').get(id) as any;
  if (!existing) {
    res.status(404).json({ error: 'Không tìm thấy hình ảnh' });
    return;
  }
  const { title, altText } = req.body || {};
  db.prepare('UPDATE media_assets SET title = ?, alt_text = ? WHERE id = ?').run(
    title ?? existing.title,
    altText ?? existing.alt_text,
    id
  );
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

app.delete('/api/admin/media/:id', requirePermission('media'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const existing = db.prepare('SELECT * FROM media_assets WHERE id = ?').get(id) as any;
  if (!existing) {
    res.status(404).json({ error: 'Không tìm thấy hình ảnh' });
    return;
  }
  if (typeof existing.url === 'string' && existing.url.startsWith('/uploads/')) {
    const fileName = path.basename(existing.url);
    const filePath = path.join(UPLOADS_DIR, fileName);
    if (fs.existsSync(filePath)) {
      fs.unlinkSync(filePath);
    }
  }
  db.prepare('DELETE FROM media_assets WHERE id = ?').run(id);
  logAudit(req.authUser!.userId, req.authUser!.email, 'DELETE_MEDIA', 'media_asset', id, { url: existing.url });
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

app.get('/api/admin/journal', requirePermission('posts'), (_req, res) => {
  const rows = db.prepare('SELECT * FROM journal_articles ORDER BY id DESC').all() as any[];
  const articles = rows.map((a) => ({
    ...a,
    tags: JSON.parse(a.tags_json || '[]'),
  }));
  res.json({ articles });
});

app.post('/api/admin/journal', requirePermission('posts'), (req: AuthedRequest, res) => {
  const b = req.body || {};
  if (!b.title_vi || !b.category) {
    res.status(400).json({ error: 'Vui lòng nhập Tiêu đề bài viết và Chuyên mục.' });
    return;
  }
  let slug = toSafeSlug(b.slug || b.title_vi);
  if (!slug) slug = `bai-viet-${Date.now()}`;
  const conflict = db.prepare('SELECT id FROM journal_articles WHERE slug = ?').get(slug);
  if (conflict) slug = `${slug}-${Date.now().toString().slice(-4)}`;

  const resInsert = db
    .prepare(`
      INSERT INTO journal_articles (slug, category, tags_json, title_vi, title_en, excerpt_vi, excerpt_en, content_vi, content_en, author, read_minutes, image_key, published)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `)
    .run(
      slug,
      b.category,
      JSON.stringify(Array.isArray(b.tags) ? b.tags : []),
      String(b.title_vi).trim(),
      String(b.title_en || b.title_vi).trim(),
      b.excerpt_vi || '',
      b.excerpt_en || b.excerpt_vi || '',
      b.content_vi || '',
      b.content_en || b.content_vi || '',
      b.author || 'Ban Biên Tập ROAR COFFEE',
      Number(b.read_minutes || 4),
      b.image_key || 'hero_roar_coffee',
      b.published === 0 || b.published === false ? 0 : 1
    );
  const newId = Number(resInsert.lastInsertRowid);
  logAudit(req.authUser!.userId, req.authUser!.email, 'CREATE_ARTICLE', 'journal_article', newId, { slug });
  scheduleSnapshotSync(db);
  res.status(201).json({ ok: true, id: newId, slug });
});

app.patch('/api/admin/journal/:id', requirePermission('posts'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const existing = db.prepare('SELECT * FROM journal_articles WHERE id = ?').get(id) as any;
  if (!existing) {
    res.status(404).json({ error: 'Không tìm thấy bài viết' });
    return;
  }
  const b = req.body || {};
  const nextSlug = b.slug ? toSafeSlug(b.slug) || existing.slug : existing.slug;
  db.prepare(`
    UPDATE journal_articles SET
      slug = ?, category = ?, tags_json = ?,
      title_vi = ?, title_en = ?, excerpt_vi = ?, excerpt_en = ?,
      content_vi = ?, content_en = ?, author = ?, read_minutes = ?,
      image_key = ?, published = ?
    WHERE id = ?
  `).run(
    nextSlug,
    b.category ?? existing.category,
    b.tags !== undefined ? JSON.stringify(b.tags) : existing.tags_json,
    b.title_vi ?? existing.title_vi,
    b.title_en ?? existing.title_en,
    b.excerpt_vi ?? existing.excerpt_vi,
    b.excerpt_en ?? existing.excerpt_en,
    b.content_vi ?? existing.content_vi,
    b.content_en ?? existing.content_en,
    b.author ?? existing.author,
    b.read_minutes !== undefined ? Number(b.read_minutes) : existing.read_minutes,
    b.image_key ?? existing.image_key,
    b.published !== undefined ? (b.published ? 1 : 0) : existing.published,
    id
  );
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_ARTICLE', 'journal_article', id, { slug: nextSlug });
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

app.delete('/api/admin/journal/:id', requirePermission('posts'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const existing = db.prepare('SELECT * FROM journal_articles WHERE id = ?').get(id) as any;
  if (!existing) {
    res.status(404).json({ error: 'Không tìm thấy bài viết' });
    return;
  }
  db.prepare('DELETE FROM journal_articles WHERE id = ?').run(id);
  logAudit(req.authUser!.userId, req.authUser!.email, 'DELETE_ARTICLE', 'journal_article', id, { slug: existing.slug });
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

// ---------- CMS SUBPAGES EDITOR (TRANG CON WEBSITE) ----------
app.get('/api/admin/pages', requirePermission('pages'), (_req, res) => {
  const rows = db.prepare('SELECT * FROM cms_pages ORDER BY group_name ASC, slug ASC').all() as any[];
  const pages = rows.map((p) => {
    let sections = [];
    try {
      sections = JSON.parse(p.sections_json || '[]');
    } catch {
      sections = [];
    }
    return { ...p, sections };
  });
  res.json({ pages });
});

app.patch('/api/admin/pages/:slug', requirePermission('pages'), (req: AuthedRequest, res) => {
  const slug = req.params.slug;
  const existing = db.prepare('SELECT * FROM cms_pages WHERE slug = ?').get(slug) as any;
  if (!existing) {
    res.status(404).json({ error: 'Không tìm thấy trang con' });
    return;
  }
  const b = req.body || {};
  db.prepare(`
    UPDATE cms_pages SET
      eyebrow_vi = ?, eyebrow_en = ?,
      title_vi = ?, title_en = ?,
      subtitle_vi = ?, subtitle_en = ?,
      body_vi = ?, body_en = ?,
      hero_image_key = ?,
      cta_label_vi = ?, cta_label_en = ?, cta_url = ?,
      sections_json = ?,
      updated_at = datetime('now')
    WHERE slug = ?
  `).run(
    b.eyebrow_vi ?? existing.eyebrow_vi,
    b.eyebrow_en ?? existing.eyebrow_en,
    b.title_vi ?? existing.title_vi,
    b.title_en ?? existing.title_en,
    b.subtitle_vi ?? existing.subtitle_vi,
    b.subtitle_en ?? existing.subtitle_en,
    b.body_vi ?? existing.body_vi,
    b.body_en ?? existing.body_en,
    b.hero_image_key ?? existing.hero_image_key,
    b.cta_label_vi ?? existing.cta_label_vi,
    b.cta_label_en ?? existing.cta_label_en,
    b.cta_url ?? existing.cta_url,
    b.sections !== undefined ? JSON.stringify(Array.isArray(b.sections) ? b.sections : []) : existing.sections_json,
    slug
  );
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_CMS_PAGE', 'cms_page', slug, {
    title_vi: b.title_vi ?? existing.title_vi,
  });
  const updated = db.prepare('SELECT * FROM cms_pages WHERE slug = ?').get(slug) as any;
  scheduleSnapshotSync(db);
  res.json({ ok: true, page: { ...updated, sections: JSON.parse(updated.sections_json || '[]') } });
});

// ---------- ADMIN TEAM & RBAC PERMISSIONS MANAGEMENT ----------
app.get('/api/admin/team', requirePermission('team'), (_req, res) => {
  const adminRows = db
    .prepare(
      "SELECT id, email, full_name, phone, role, admin_role, admin_permissions_json, member_code, tier, created_at, password_hash FROM users WHERE role = 'admin' ORDER BY id ASC"
    )
    .all() as any[];

  const admins = adminRows.map((u) => {
    const rbac = resolveEffectiveAdminPermissions(u);
    return {
      id: u.id,
      email: u.email,
      fullName: u.full_name,
      phone: u.phone,
      role: u.role,
      adminRole: rbac.adminRole,
      adminPermissions: rbac.adminPermissions,
      memberCode: u.member_code,
      tier: u.tier,
      createdAt: u.created_at,
      hasPassword: Boolean(u.password_hash && String(u.password_hash).includes(':')),
    };
  });

  const nonAdmins = db
    .prepare(
      "SELECT id, email, full_name, phone, role, member_code FROM users WHERE role != 'admin' ORDER BY id DESC LIMIT 100"
    )
    .all() as any[];

  const auditLogs = db.prepare('SELECT * FROM audit_logs ORDER BY id DESC LIMIT 50').all();

  res.json({ admins, nonAdmins, auditLogs });
});

app.post('/api/admin/team', requirePermission('team'), (req: AuthedRequest, res) => {
  const { email, fullName, phone = '', password, adminRole = 'content_editor', permissions } = req.body || {};
  if (!email) {
    res.status(400).json({ error: 'Vui lòng nhập email quản trị viên.' });
    return;
  }
  const normalizedEmail = String(email).trim().toLowerCase();
  const validRole = Object.keys(ADMIN_ROLE_PRESETS).includes(adminRole) ? adminRole : 'custom_staff';
  const resolvedPerms: string[] =
    validRole === 'super_admin'
      ? [...ALL_ADMIN_PERMISSIONS]
      : Array.isArray(permissions)
        ? permissions.filter((p): p is string => (ALL_ADMIN_PERMISSIONS as readonly string[]).includes(p))
        : ADMIN_ROLE_PRESETS[validRole] || ['overview'];

  const existing = db.prepare('SELECT * FROM users WHERE email = ?').get(normalizedEmail) as any;
  if (existing) {
    const actorRow = db
      .prepare('SELECT id, email, role, admin_role, admin_permissions_json FROM users WHERE id = ?')
      .get(req.authUser!.userId) as any;
    const actorRbac = resolveEffectiveAdminPermissions(actorRow);
    const targetRbac = resolveEffectiveAdminPermissions(existing);

    if (existing.role === 'admin' && targetRbac.adminRole === 'super_admin' && actorRbac.adminRole !== 'super_admin') {
      res.status(403).json({ error: 'Chỉ Super Admin mới có thể chỉnh sửa tài khoản Super Admin.' });
      return;
    }
    if (validRole === 'super_admin' && actorRbac.adminRole !== 'super_admin') {
      res.status(403).json({ error: 'Chỉ Super Admin mới có thể cấp quyền Super Admin.' });
      return;
    }

    const rawPromotePassword = password !== undefined && password !== null ? String(password) : '';
    if (rawPromotePassword.length > 0 && rawPromotePassword.length < 8) {
      res.status(400).json({ error: 'Mật khẩu mới phải có tối thiểu 8 ký tự.' });
      return;
    }

    db.prepare(`
      UPDATE users SET role = 'admin', admin_role = ?, admin_permissions_json = ?, email_verified = 1 WHERE id = ?
    `).run(validRole, JSON.stringify(resolvedPerms), existing.id);

    if (rawPromotePassword.length >= 8) {
      db.prepare('UPDATE users SET password_hash = ?, reset_token = NULL, reset_expires = NULL WHERE id = ?').run(
        hashPassword(rawPromotePassword),
        existing.id
      );
    }

    logAudit(req.authUser!.userId, req.authUser!.email, 'PROMOTE_ADMIN_MEMBER', 'user', existing.id, {
      email: normalizedEmail,
      adminRole: validRole,
      permissions: resolvedPerms,
      passwordSet: rawPromotePassword.length >= 8,
    });
    res.status(200).json({ ok: true, id: existing.id, promoted: true });
    return;
  }

  if (!fullName || !password || String(password).length < 8) {
    res.status(400).json({ error: 'Tài khoản mới cần Họ tên và Mật khẩu tối thiểu 8 ký tự.' });
    return;
  }

  const memberCode = `RC-ADM-${Math.floor(1000 + Math.random() * 9000)}`;
  const ins = db
    .prepare(`
      INSERT INTO users (
        email, password_hash, full_name, phone, role, admin_role, admin_permissions_json,
        member_code, tier, email_verified
      ) VALUES (?, ?, ?, ?, 'admin', ?, ?, ?, 'ROAR Gold', 1)
    `)
    .run(
      normalizedEmail,
      hashPassword(String(password)),
      String(fullName).trim(),
      String(phone || '').trim(),
      validRole,
      JSON.stringify(resolvedPerms),
      memberCode
    );

  const newId = Number(ins.lastInsertRowid);
  logAudit(req.authUser!.userId, req.authUser!.email, 'CREATE_ADMIN_MEMBER', 'user', newId, {
    email: normalizedEmail,
    adminRole: validRole,
    permissions: resolvedPerms,
  });
  res.status(201).json({ ok: true, id: newId });
});

app.patch('/api/admin/team/:id', requirePermission('team'), (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const target = db.prepare('SELECT * FROM users WHERE id = ?').get(id) as any;
  if (!target) {
    res.status(404).json({ error: 'Không tìm thấy thành viên' });
    return;
  }

  const { adminRole, permissions, revokeAdmin, fullName } = req.body || {};
  const superAdminCount = (
    db.prepare("SELECT COUNT(*) as c FROM users WHERE role = 'admin' AND admin_role = 'super_admin'").get() as { c: number }
  ).c;

  if (revokeAdmin) {
    if (target.id === req.authUser!.userId) {
      res.status(400).json({ error: 'Không thể tự thu hồi quyền quản trị của chính tài khoản đang đăng nhập.' });
      return;
    }
    if (target.admin_role === 'super_admin' && superAdminCount <= 1) {
      res.status(400).json({ error: 'Phải giữ lại ít nhất 1 Quản trị Tối cao (Super Admin).' });
      return;
    }
    db.prepare("UPDATE users SET role = 'customer', admin_role = 'none', admin_permissions_json = '[]' WHERE id = ?").run(id);
    logAudit(req.authUser!.userId, req.authUser!.email, 'REVOKE_ADMIN_MEMBER', 'user', id, { email: target.email });
    res.json({ ok: true });
    return;
  }

  const nextRole =
    adminRole && Object.keys(ADMIN_ROLE_PRESETS).includes(adminRole)
      ? String(adminRole)
      : target.admin_role && target.admin_role !== 'none'
        ? target.admin_role
        : 'custom_staff';

  if (target.admin_role === 'super_admin' && nextRole !== 'super_admin' && superAdminCount <= 1) {
    res.status(400).json({ error: 'Không thể hạ cấp Quản trị Tối cao cuối cùng trong hệ thống.' });
    return;
  }

  const nextPerms: string[] =
    nextRole === 'super_admin'
      ? [...ALL_ADMIN_PERMISSIONS]
      : Array.isArray(permissions)
        ? permissions.filter((p): p is string => (ALL_ADMIN_PERMISSIONS as readonly string[]).includes(p))
        : ADMIN_ROLE_PRESETS[nextRole] || JSON.parse(target.admin_permissions_json || '[]');

  if (target.id === req.authUser!.userId && nextRole !== 'super_admin' && !nextPerms.includes('team')) {
    res.status(400).json({ error: 'Không thể tự bỏ quyền Phân quyền Thành viên của chính bạn.' });
    return;
  }

  db.prepare(`
    UPDATE users SET
      role = 'admin',
      admin_role = ?,
      admin_permissions_json = ?,
      full_name = ?
    WHERE id = ?
  `).run(nextRole, JSON.stringify(nextPerms), fullName ? String(fullName).trim() : target.full_name, id);

  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_ADMIN_RBAC', 'user', id, {
    email: target.email,
    adminRole: nextRole,
    permissions: nextPerms,
  });
  res.json({ ok: true });
});

app.post('/api/admin/users/:id/reset-password', requireAdmin, (req: AuthedRequest, res) => {
  const id = Number(req.params.id);
  const newPassword = String(req.body?.newPassword || '');
  if (!Number.isInteger(id) || id <= 0) {
    res.status(400).json({ error: 'ID tài khoản không hợp lệ.' });
    return;
  }
  if (newPassword.length < 8) {
    res.status(400).json({ error: 'Mật khẩu mới phải có tối thiểu 8 ký tự.' });
    return;
  }

  const actorRow = db
    .prepare('SELECT id, email, role, admin_role, admin_permissions_json FROM users WHERE id = ?')
    .get(req.authUser!.userId) as any;
  if (!actorRow || actorRow.role !== 'admin') {
    res.status(403).json({ error: 'Forbidden: Administrator role required' });
    return;
  }

  const target = db
    .prepare('SELECT id, email, full_name, role, admin_role, admin_permissions_json FROM users WHERE id = ?')
    .get(id) as any;
  if (!target) {
    res.status(404).json({ error: 'Không tìm thấy tài khoản.' });
    return;
  }

  const actorRbac = resolveEffectiveAdminPermissions(actorRow);
  const isActorSuper = actorRbac.adminRole === 'super_admin';

  if (target.role === 'admin') {
    if (!isActorSuper && !actorRbac.adminPermissions.includes('team')) {
      res.status(403).json({ error: 'Bạn cần quyền Phân quyền Thành viên (team) để đặt lại mật khẩu Quản trị viên.' });
      return;
    }
    const targetRbac = resolveEffectiveAdminPermissions(target);
    if (targetRbac.adminRole === 'super_admin' && !isActorSuper) {
      res.status(403).json({ error: 'Chỉ Super Admin mới được phép đặt lại mật khẩu của tài khoản Super Admin.' });
      return;
    }
  } else {
    const canManageCustomers =
      isActorSuper ||
      actorRbac.adminPermissions.includes('customers') ||
      actorRbac.adminPermissions.includes('team');
    if (!canManageCustomers) {
      res.status(403).json({ error: 'Bạn chưa được cấp quyền Khách hàng hoặc Phân quyền Thành viên để đặt lại mật khẩu.' });
      return;
    }
  }

  db.prepare('UPDATE users SET password_hash = ?, reset_token = NULL, reset_expires = NULL WHERE id = ?').run(
    hashPassword(newPassword),
    id
  );

  logAudit(req.authUser!.userId, req.authUser!.email, 'ADMIN_RESET_PASSWORD', 'user', id, {
    targetEmail: target.email,
    targetRole: target.role,
  });

  createUserNotification(id, {
    titleVi: 'Mật khẩu tài khoản vừa được Quản trị viên đặt lại',
    titleEn: 'Your account password was reset by an administrator',
    messageVi: 'Quản trị viên ROAR COFFEE vừa đặt lại mật khẩu đăng nhập cho tài khoản của bạn. Vui lòng đổi lại mật khẩu cá nhân sau khi đăng nhập nếu cần.',
    messageEn: 'A ROAR COFFEE administrator reset your sign-in password. You may change it from your Account settings after signing in.',
    category: 'system',
    linkUrl: '/account',
  });

  res.json({ ok: true });
});

app.get('/api/admin/settings', requirePermission('settings'), (_req, res) => {
  const rows = db.prepare('SELECT key, value FROM site_settings').all() as Array<{ key: string; value: string }>;
  const settings: Record<string, string> = {};
  for (const r of rows) settings[r.key] = r.value;
  res.json({ settings });
});

app.patch('/api/admin/settings', requirePermission('settings'), (req: AuthedRequest, res) => {
  const rawBody = (req.body || {}) as Record<string, unknown>;
  const updates = (
    rawBody.settings && typeof rawBody.settings === 'object' && !Array.isArray(rawBody.settings)
      ? rawBody.settings
      : rawBody
  ) as Record<string, unknown>;
  const urlKeys = new Set(['facebook_url', 'instagram_url', 'tiktok_url', 'youtube_url', 'zalo_url']);
  const upsert = db.prepare('INSERT INTO site_settings (key, value) VALUES (?, ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value');
  for (const [k, rawVal] of Object.entries(updates)) {
    if (rawVal && typeof rawVal === 'object') continue;
    const val = String(rawVal ?? '').trim();
    if (urlKeys.has(k) && val) {
      if (!/^https?:\/\//i.test(val)) {
        res.status(400).json({ error: `Liên kết ${k} phải bắt đầu bằng https:// hoặc http://` });
        return;
      }
    }
    upsert.run(k, val);
  }
  logAudit(req.authUser!.userId, req.authUser!.email, 'UPDATE_SITE_SETTINGS', 'site_settings', 'global', updates);
  scheduleSnapshotSync(db);
  res.json({ ok: true });
});

// ---------- PORTABLE GITHUB SNAPSHOT SYNC / DOWNLOAD / RESTORE ----------
app.post('/api/admin/snapshot/sync', requirePermission('settings'), (req: AuthedRequest, res) => {
  const snap = exportCmsSnapshotToDisk(db);
  logAudit(req.authUser!.userId, req.authUser!.email, 'SYNC_CMS_SNAPSHOT', 'snapshot', 'roar-cms-snapshot.json', {
    products: snap.tables.products.length,
    origins: snap.tables.coffee_origins.length,
    pages: snap.tables.cms_pages.length,
    articles: snap.tables.journal_articles.length,
  });
  res.json({
    ok: true,
    exportedAt: snap.exportedAt,
    counts: {
      products: snap.tables.products.length,
      origins: snap.tables.coffee_origins.length,
      pages: snap.tables.cms_pages.length,
      articles: snap.tables.journal_articles.length,
      personalities: snap.tables.personalities.length,
      promotions: snap.tables.promotions.length,
      media: snap.tables.media_assets.length,
    },
  });
});

app.get('/api/admin/snapshot/download', requirePermission('settings'), (_req, res) => {
  const snap = buildCmsSnapshot(db);
  res.setHeader('Content-Type', 'application/json; charset=utf-8');
  res.setHeader('Content-Disposition', 'attachment; filename="roar-coffee-cms-backup.json"');
  res.send(JSON.stringify(snap, null, 2));
});

app.post('/api/admin/snapshot/restore', requirePermission('settings'), (req: AuthedRequest, res) => {
  const body = req.body || {};
  const restored = restoreFromSnapshot(db, {
    force: true,
    snapshotData: body && body.tables ? body : undefined,
  });
  if (!restored) {
    res.status(400).json({ error: 'Không tìm thấy tệp Snapshot hợp lệ để khôi phục.' });
    return;
  }
  exportCmsSnapshotToDisk(db);
  logAudit(req.authUser!.userId, req.authUser!.email, 'RESTORE_CMS_SNAPSHOT', 'snapshot', 'roar-cms-snapshot.json', {});
  res.json({ ok: true });
});

// ---------- ADMIN AI AUTO-TRANSLATION (VI -> EN) & VIETCOMBANK EXCHANGE RATE SYNC ----------
app.post('/api/admin/translate-vi-en', requirePermission('products', 'posts', 'pages', 'brand'), async (req, res) => {
  try {
    const translations = await translateProductViToEn(req.body || {});
    res.json({ ok: true, translations });
  } catch (err: any) {
    if (err instanceof GeminiTranslationError) {
      res.status(err.status).json({ error: err.message, code: err.code });
      return;
    }
    res.status(500).json({ error: err?.message || 'Lỗi dịch tự động VI → EN' });
  }
});

app.post('/api/admin/exchange-rate/vietcombank/sync', requirePermission('products', 'settings'), async (req: AuthedRequest, res) => {
  const { rateMode, applyToAllProducts } = req.body || {};
  const validMode: VcbRateMode | undefined =
    rateMode === 'buy' || rateMode === 'transfer' || rateMode === 'sell' ? rateMode : undefined;
  if (validMode) {
    db.prepare(
      "INSERT INTO site_settings (key, value) VALUES ('vcb_rate_mode', ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value"
    ).run(validMode);
  }
  const rate = await getVietcombankUsdRate(db, { force: true, modeOverride: validMode });

  let updatedProducts = 0;
  if (applyToAllProducts) {
    const allProducts = db.prepare('SELECT id, price_vnd, variants_json, pricing_tiers_json FROM products').all() as Array<{
      id: number;
      price_vnd: number;
      variants_json: string;
      pricing_tiers_json: string;
    }>;
    const updStmt = db.prepare('UPDATE products SET price_usd = ?, variants_json = ?, pricing_tiers_json = ? WHERE id = ?');
    const tx = db.transaction(() => {
      for (const p of allProducts) {
        const nextUsd = convertVndToUsdByRate(p.price_vnd, rate.activeRate);
        let variants: any[] = [];
        try {
          variants = JSON.parse(p.variants_json || '[]');
        } catch {
          variants = [];
        }
        const nextVariants = Array.isArray(variants)
          ? variants.map((v) => ({
              ...v,
              priceUsd:
                Number(v.priceVnd) > 0
                  ? convertVndToUsdByRate(Number(v.priceVnd), rate.activeRate)
                  : Number(v.priceUsd || 0),
            }))
          : [];

        let pricingTiers: any[] = [];
        try {
          pricingTiers = JSON.parse(p.pricing_tiers_json || '[]');
        } catch {
          pricingTiers = [];
        }
        const nextTiers = Array.isArray(pricingTiers)
          ? pricingTiers.map((t) => ({
              ...t,
              priceUsd:
                Number(t.priceVnd) > 0
                  ? convertVndToUsdByRate(Number(t.priceVnd), rate.activeRate)
                  : Number(t.priceUsd || 0),
            }))
          : [];

        updStmt.run(nextUsd, JSON.stringify(nextVariants), JSON.stringify(nextTiers), p.id);
        updatedProducts += 1;
      }
    });
    tx();
    logAudit(req.authUser!.userId, req.authUser!.email, 'SYNC_VCB_RATES_CATALOG', 'products', 'all', {
      activeRate: rate.activeRate,
      rateMode: rate.rateMode,
      updatedProducts,
    });
  }
  scheduleSnapshotSync(db);
  res.json({ ok: true, rate, updatedProducts });
});

// ---------- VITE / STATIC SERVING ----------
async function startServer() {
  const httpServer = createHttpServer(app);
  const distDir = path.resolve(process.cwd(), 'dist');
  const useProdStatic = IS_PROD && fs.existsSync(distDir);

  if (!useProdStatic) {
    const vite = await createViteServer({
      server: {
        middlewareMode: true,
        allowedHosts: true,
        // Attach Vite HMR to the same HTTP server that serves Express middleware.
        hmr: { server: httpServer },
      },
      appType: 'spa',
    });
    app.use(vite.middlewares);
  } else {
    app.use('/src/assets', express.static(path.resolve(process.cwd(), 'src/assets')));
    app.use(express.static(distDir));
    app.get('*', (_req, res) => {
      res.sendFile(path.join(distDir, 'index.html'));
    });
  }

  httpServer.listen(PORT, '0.0.0.0', () => {
    console.log(`ROAR COFFEE platform listening on http://localhost:${PORT}`);
  });
}

startServer();
