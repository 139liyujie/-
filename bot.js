const { Bot, InlineKeyboard, InputFile } = require("grammy");
const { TelegramClient } = require("telegram");
const { StringSession } = require("telegram/sessions");
const { Api } = require("telegram/tl");
const { BinaryReader } = require("telegram/extensions");
const http = require("http");
const https = require("https");
const fs = require("fs");
const Database = require("better-sqlite3");
const path = require("path");
const crypto = require("crypto");
const AdmZip = require("adm-zip");
const { getBinding, setBinding, deleteBinding, getNewsBinding, setNewsBinding, deleteNewsBinding, insertPost, upsertUser, getUser, getUserByUsername, getUserLang, countUsers, listUsers, clearPosts, addAdmin, removeAdmin, listAdmins, isAdmin, getBotEnabled, setBotEnabled, hasPostByFileId, backupPosts, restorePostsFromBackup, hasBackup, addUnique, hasUnique, countPosts, listPosts, ensureWebAdmin, verifyWebAdmin, addUsernames, listUsernames, listAllUsernames, countAllUsernames, listAllDistinctUsernames, countDistinctUsernames, hasUsername, deleteUsername, insertFailedPost, listFailedPosts, countFailedPosts, deleteFailedByFileId, addAccount, listAccounts, getAllAccounts, countAccounts, deleteAccount, getAccountByPhone, getGlobalExtractMode, setGlobalExtractMode, getApiConfig, setApiConfig, addWebSession, getWebSession, deleteWebSession, addQrToken, getQrToken, updateQrToken, deleteQrToken, setAccountStatus, updateAccountSession, addInviteLink, getLatestInviteLink, getInviteByLink, addReferral, listReferrals, countReferrals, listInviteLinksByUser, getLinkBinding, setLinkBinding, deleteLinkBinding, listReferralsByChat, countReferralsByChat, deleteInviteLinksByUserChat, clearReferralsByInviterChat, ensureJoinRequest, setJoinRequestCode, setJoinRequestGuarantor, setJoinRequestStatus, addChristmasWish, hasChristmasWish, getChristmasWish, getLatestChristmasWish, getBusinessAntiEditDelete, setBusinessAntiEditDelete, getSelectedCategory, setSelectedCategory, addSupport, isSupport, addRegAnchor, listRegAnchors, listInvitersByChat, getGroupNoApproval, setGroupNoApproval } = require("./db");

const SUPER_ADMIN_ID = 7902147860;
// 默认使用 Telegram Android 的官方 API ID/Hash，如果数据库有配置则覆盖
const DEFAULT_API_ID = 22309210;
const DEFAULT_API_HASH = "b53b92a4de2a6681d141440ea2c4208d";

// 辅助函数：获取当前使用的 API 配置
function getCurrentApiConfig() {
  const custom = getApiConfig();
  if (custom) return custom;
  return { apiId: Number(process.env.API_ID) || DEFAULT_API_ID, apiHash: process.env.API_HASH || DEFAULT_API_HASH };
}

const userAddAdminMode = new Map();
const userAddSupportMode = new Map();
const userJoinChannelMode = new Map();
const userLoginState = new Map();
const userSteps = new Map();
const businessConnections = new Map();
const businessMessageCache = new Map();
const REG_DATA_URL = "https://raw.githubusercontent.com/lastochkin-group/telegram-account-age-estimator/main/ages.json";
const regDataCache = { data: null, ts: 0 };

// 第二个机器人：邀请链接机器人
const linkToken = process.env.LINK_BOT_TOKEN;
let linkBot = null;
if (!linkToken) {
  console.error("必须设置环境变量 LINK_BOT_TOKEN");
} else {
  linkBot = new Bot(linkToken);
}

let LINK_BOT_ID = 0;
const membershipCache = new Map();
async function ensureLinkBotId(api) {
  if (LINK_BOT_ID) return LINK_BOT_ID;
  try { const me = await api.getMe(); LINK_BOT_ID = me.id || 0; } catch {}
  return LINK_BOT_ID;
}
async function isBotInChat(api, chatId) {
  const now = Date.now();
  const c = membershipCache.get(chatId);
  if (c && (now - c.ts) < 10*60*1000) return c.ok;
  let ok = true;
  try {
    const id = await ensureLinkBotId(api);
    const m = await api.getChatMember(chatId, id);
    const st = m.status;
    ok = st === "member" || st === "administrator" || st === "creator";
  } catch { ok = false; }
  membershipCache.set(chatId, { ok, ts: now });
  return ok;
}

if (linkBot) {
  const linkKeyboard = new InlineKeyboard()
    .text("我的邀请链接", "my_links").row()
    .text("查看我的下级", "my_refs");
  
  linkBot.command("start", async (ctx) => {
    if (ctx.chat?.type !== "private") return;
    if (ctx.from) upsertUser(ctx.from.id, ctx.from.first_name, ctx.from.last_name, ctx.from.username);
    const uid = ctx.from?.id || 0;
    const name = ((ctx.from?.first_name || "") + " " + (ctx.from?.last_name || "")).trim() || "未设置";
    const uname = ctx.from?.username || "无";
    const text = `┏━━UID：${uid}
┣━━Name：${name}
┗━━Uname：@${uname}`;
    await ctx.reply(text, { reply_markup: linkKeyboard });
  });
  
  // 绑定后台群（LinkBot 专用）
  linkBot.command("star后台", async (ctx) => {
    const type = ctx.chat?.type;
    if (type === "private") { await ctx.reply("请在群组或频道中使用此命令"); return; }
    const fromId = ctx.from?.id || 0;
    let ok = isAdmin(fromId);
    if (!ok) {
      try {
        const m = await ctx.api.getChatMember(ctx.chat.id, fromId);
        const st = m.status;
        ok = st === "administrator" || st === "creator";
      } catch {}
    }
    if (!ok) return;
    const chat = ctx.chat;
    setLinkBinding(chat.id, chat.title || "");
    await ctx.reply(`✅ 绑定成功！当前群组/频道 [${chat.title || "未命名"}] 已设为邀请后台。`);
  });
  
  linkBot.command("关闭审核", async (ctx) => {
    const type = ctx.chat?.type;
    if (type !== "supergroup" && type !== "group") return;
    const chatId = ctx.chat.id;
    try {
      const me = await ctx.api.getChatMember(chatId, ctx.from.id);
      if (me.status !== "creator") { await ctx.reply("仅群创建者可执行此命令"); return; }
    } catch { return; }
    setGroupNoApproval(chatId, true);
    const inviters = listInvitersByChat(chatId);
    let okCount = 0;
    for (const uid of inviters) {
      try {
        const link = await ctx.api.createChatInviteLink(chatId, { name: `UID:${uid}`, creates_join_request: false });
        addInviteLink(chatId, uid, link.invite_link, (await ctx.api.getChat(chatId)).title || "");
        okCount++;
      } catch {}
    }
    await ctx.reply(`已关闭审核，并为 ${okCount} 位用户生成免审核专属链接。\n公开链接审核设置无法由机器人更改，请在群设置中关闭“加入请求”。`);
  });
  
  linkBot.command("link", async (ctx) => {
    const type = ctx.chat?.type;
    if (type !== "supergroup" && type !== "group") return;
    const chat = ctx.chat;
    const txt = ctx.message?.text || "";
    const args = txt.split(/\s+/).slice(1);
    const noApproval = getGroupNoApproval(chat.id);
    // 若带用户名参数，则为管理员为他人生成
    if (args.length > 0) {
      const handle = args[0].replace(/^@/, "");
      const target = getUserByUsername(handle);
      if (!target) { await ctx.reply("未找到该用户"); return; }
      try {
        const me = await ctx.api.getChatMember(chat.id, ctx.from.id);
        const st = me.status;
        if (st !== "administrator" && st !== "creator") { await ctx.reply("仅管理员可为他人生成链接"); return; }
      } catch { return; }
      try {
        const link = await ctx.api.createChatInviteLink(chat.id, {
          name: `UID:${target.id}`,
          creates_join_request: !noApproval
        });
        addInviteLink(chat.id, target.id, link.invite_link, `@${handle}`);
        await ctx.reply(`新的专属邀请链接：\n${link.invite_link}`);
      } catch (e) {
        await ctx.reply("无法生成邀请链接，请确保我在群组是管理员并拥有创建邀请链接权限。");
      }
      return;
    }
    // 无参数则为自己生成
    const inviterId = ctx.from?.id || 0;
    if (!inviterId) return;
    const old = getLatestInviteLink(chat.id, inviterId);
    if (old && old.invite_link) {
      await ctx.reply(`你的专属邀请链接：\n${old.invite_link}`);
      return;
    }
    try {
      const link = await ctx.api.createChatInviteLink(chat.id, {
        name: `UID:${inviterId}`,
        creates_join_request: !noApproval
      });
      addInviteLink(chat.id, inviterId, link.invite_link, `@${ctx.from?.username || ""}`);
      await ctx.reply(`你的专属邀请链接：\n${link.invite_link}\n提示：管理员需开启“加入请求”以便统计邀请。`);
    } catch (e) {
      await ctx.reply("无法生成邀请链接，请确保我在群组是管理员并拥有创建邀请链接权限。");
    }
  });
  
  linkBot.on("chat_join_request", async (ctx) => {
    const req = ctx.update.chat_join_request;
    const chatId = req.chat.id;
    const invitee = req.from;
    const linkObj = req.invite_link;
    try {
      await ctx.api.approveChatJoinRequest(chatId, invitee.id);
    } catch {}
    const linkStr = linkObj?.invite_link || "";
    const rec = linkStr ? getInviteByLink(linkStr) : null;
    if (invitee) upsertUser(invitee.id, invitee.first_name, invitee.last_name, invitee.username);
    if (rec && rec.inviter_id) {
      addReferral(chatId, rec.inviter_id, invitee.id, linkStr);
      const cnt = countReferrals(rec.inviter_id);
      const inviter = getUser(rec.inviter_id);
      const inviterName = ((inviter?.first_name || "") + " " + (inviter?.last_name || "")).trim() || (inviter?.username ? "@"+inviter.username : String(rec.inviter_id));
      const inviteeName = ((invitee.first_name || "") + (invitee.last_name ? " "+invitee.last_name : "")).trim() || (invitee.username ? "@"+invitee.username : String(invitee.id));
      const text = `🎉 恭喜 <a href="tg://user?id=${rec.inviter_id}">${inviterName}</a> 邀请 <a href="tg://user?id=${invitee.id}">${inviteeName}</a> 加入群组\n📈 当前已邀请 <b>${cnt}</b> 人`;
      await ctx.api.sendMessage(chatId, text, { parse_mode: "HTML" });
    }
  });
  
  linkBot.callbackQuery("my_links", async (ctx) => {
    const uid = ctx.from?.id || 0;
    const rows = listInviteLinksByUser(uid) || [];
    if (!rows.length) { await ctx.answerCallbackQuery({ text: "暂无邀请链接" }); return; }
    const kb = new InlineKeyboard();
    for (const r of rows) {
      const show = await isBotInChat(ctx.api, r.chat_id);
      if (show) {
        kb.text((r.name || "未命名") + `(${r.chat_id})`, `show_link:${r.chat_id}`).row();
      }
    }
    try { await ctx.editMessageText("请选择群组以查看你的专属邀请链接：", { reply_markup: kb }); } catch { await ctx.reply("请选择群组以查看你的专属邀请链接：", { reply_markup: kb }); }
    await ctx.answerCallbackQuery({ text: "✅" });
  });
  
  linkBot.callbackQuery(/show_link:(-?\d+)/, async (ctx) => {
    const chatId = parseInt(ctx.match[1]);
    const uid = ctx.from?.id || 0;
    const row = getLatestInviteLink(chatId, uid);
    await ctx.answerCallbackQuery({ text: row && row.invite_link ? "✅" : "未找到链接" });
    if (row && row.invite_link) {
      await ctx.reply(`群组(${chatId}) 邀请链接：\n${row.invite_link}`);
    }
  });
  
  // 私聊“查看我的下级”先选择群组
  linkBot.callbackQuery("my_refs", async (ctx) => {
    const uid = ctx.from?.id || 0;
    const rows = listInviteLinksByUser(uid) || [];
    if (!rows.length) { await ctx.answerCallbackQuery({ text: "暂无邀请记录" }); return; }
    const kb = new InlineKeyboard();
    for (const r of rows) {
      const show = await isBotInChat(ctx.api, r.chat_id);
      if (show) {
        kb.text((r.name || "未命名") + `(${r.chat_id})`, `refs_for_chat:${r.chat_id}:1:10`).row();
      }
    }
    try { await ctx.editMessageText("请选择群组以查看你在该群的邀请下级：", { reply_markup: kb }); } catch { await ctx.reply("请选择群组以查看你在该群的邀请下级：", { reply_markup: kb }); }
    await ctx.answerCallbackQuery({ text: "✅" });
  });
  
  linkBot.callbackQuery(/refs_for_chat:(-?\d+):(\d+):(\d+)/, async (ctx) => {
    const chatId = parseInt(ctx.match[1]);
    const page = parseInt(ctx.match[2]);
    const limit = parseInt(ctx.match[3]);
    const uid = ctx.from?.id || 0;
    const total = countReferralsByChat(uid, chatId);
    const max = Math.max(1, Math.ceil(total / limit));
    if (page < 1) { await ctx.answerCallbackQuery({ text: "已经是第一页", show_alert: true }); return; }
    if (page > max) { await ctx.answerCallbackQuery({ text: "别点了.啥也没有啊", show_alert: true }); return; }
    const offset = (page - 1) * limit;
    const rows = listReferralsByChat(uid, chatId, limit, offset);
    const inviter = getUser(uid);
    const name = ((inviter?.first_name || "") + " " + (inviter?.last_name || "")).trim() || (inviter?.username ? "@"+inviter.username : "未设置昵称");
    const unameOut = inviter?.username ? "@"+inviter.username : "无";
    const latest = getLatestInviteLink(chatId, uid);
    const regTs = latest && latest.created_at ? latest.created_at : 0;
    const d = new Date(regTs * 1000);
    const Y = d.getFullYear();
    const M = String(d.getMonth()+1).padStart(2,"0");
    const D = String(d.getDate()).padStart(2,"0");
    const h = String(d.getHours()).padStart(2,"0");
    const m2 = String(d.getMinutes()).padStart(2,"0");
    const s = String(d.getSeconds()).padStart(2,"0");
    const regStr = regTs ? `${Y}-${M}-${D} ${h}:${m2}:${s}` : "未知";
    const head = `账号：${uid}\n昵称：${name}\n用户名：${unameOut}\n邀请数量：${total}\n注册时间：${regStr}\n📊 邀请统计（第 ${page} / ${max} 页）`;
    const lines = rows.map((r, i) => {
      const u = getUser(r.invitee_id);
      const nick = ((u?.first_name || "") + " " + (u?.last_name || "")).trim() || (u?.username ? "@"+u.username : "未设置昵称");
      return `${i+1}. <a href="tg://user?id=${r.invitee_id}">${nick}</a>`;
    });
    const body = lines.join("\n");
    const kb = new InlineKeyboard()
      .text("◀️ 上一页", `refs_for_chat:${chatId}:${page-1}:${limit}`)
      .text("下一页 ▶️", `refs_for_chat:${chatId}:${page+1}:${limit}`)
      .row().text("返回", "user_back_refs");
    try { await ctx.editMessageText(head + "\n" + body, { reply_markup: kb, parse_mode: "HTML" }); } catch { await ctx.reply(head + "\n" + body, { reply_markup: kb, parse_mode: "HTML" }); }
    await ctx.answerCallbackQuery({ text: "✅" });
  });
  linkBot.callbackQuery("user_back_refs", async (ctx) => {
    const uid = ctx.from?.id || 0;
    const rows = listInviteLinksByUser(uid) || [];
    if (!rows.length) { await ctx.answerCallbackQuery({ text: "暂无邀请记录" }); return; }
    const kb = new InlineKeyboard();
    for (const r of rows) {
      const show = await isBotInChat(ctx.api, r.chat_id);
      if (show) {
        kb.text((r.name || "未命名") + `(${r.chat_id})`, `refs_for_chat:${r.chat_id}:1:10`).row();
      }
    }
    try { await ctx.editMessageText("请选择群组以查看你在该群的邀请下级：", { reply_markup: kb }); } catch { await ctx.reply("请选择群组以查看你在该群的邀请下级：", { reply_markup: kb }); }
    await ctx.answerCallbackQuery({ text: "✅" });
  });
  
  // 后台群查询：查询 @username
  linkBot.on("message:text", async (ctx, next) => {
    const text = ctx.message.text || "";
    const type = ctx.chat?.type;
    if (type !== "supergroup" && type !== "group" && type !== "channel") return next();
    const lb = getLinkBinding();
    const fromId = ctx.from?.id || 0;
    let ok = !!lb && lb.groupId === ctx.chat.id;
    if (!ok) {
      ok = isAdmin(fromId);
      if (!ok) {
        try {
          const m = await ctx.api.getChatMember(ctx.chat.id, fromId);
          const st = m.status;
          ok = st === "administrator" || st === "creator";
        } catch {}
      }
    }
    if (!ok) return next();
    const m = text.match(/^查询\s*(@?[_a-zA-Z0-9]{3,})$/);
    if (!m) return next();
    const uname = m[1];
    const user = getUserByUsername(uname);
    if (!user) { await ctx.reply("未找到该用户"); return; }
    const kb = new InlineKeyboard()
      .text("查看他下级", `admin_refs_user:${user.id}:${ctx.chat.id}:1:10`).row()
      .text("他的链接管理", `admin_link_manage:${user.id}:${ctx.chat.id}`).row()
      .text("导出文件", `admin_export_refs:${user.id}:${ctx.chat.id}`);
    const name = ((user.first_name || "") + " " + (user.last_name || "")).trim() || (user.username ? "@"+user.username : "未设置昵称");
    const unameOut = user.username ? "@"+user.username : "无";
    const inviteCnt = countReferralsByChat(user.id, ctx.chat.id);
    const latest = getLatestInviteLink(ctx.chat.id, user.id);
    const regTs = latest && latest.created_at ? latest.created_at : 0;
    const d = new Date(regTs * 1000);
    const Y = d.getFullYear();
    const M = String(d.getMonth()+1).padStart(2,"0");
    const D = String(d.getDate()).padStart(2,"0");
    const h = String(d.getHours()).padStart(2,"0");
    const m2 = String(d.getMinutes()).padStart(2,"0");
    const s = String(d.getSeconds()).padStart(2,"0");
    const regStr = regTs ? `${Y}-${M}-${D} ${h}:${m2}:${s}` : "未知";
    const msg = `账号：${user.id}\n昵称：${name}\n用户名：${unameOut}\n邀请数量：${inviteCnt}\n注册时间：${regStr}`;
    await ctx.reply(msg, { reply_markup: kb });
  });
  
  // 管理端查看某用户在指定群的下级
  linkBot.callbackQuery(/admin_refs_user:(\d+):(-?\d+):(\d+):(\d+)/, async (ctx) => {
    const uid = parseInt(ctx.match[1]);
    const chatId = parseInt(ctx.match[2]);
    const page = parseInt(ctx.match[3]);
    const limit = parseInt(ctx.match[4]);
    const total = countReferralsByChat(uid, chatId);
    const max = Math.max(1, Math.ceil(total / limit));
    if (page < 1) { await ctx.answerCallbackQuery({ text: "已经是第一页", show_alert: true }); return; }
    if (page > max) { await ctx.answerCallbackQuery({ text: "已经是最后一页", show_alert: true }); return; }
    const offset = (page - 1) * limit;
    const rows = listReferralsByChat(uid, chatId, limit, offset);
    const inviter = getUser(uid);
    const name = ((inviter?.first_name || "") + " " + (inviter?.last_name || "")).trim() || (inviter?.username ? "@"+inviter.username : "未设置昵称");
    const unameOut = inviter?.username ? "@"+inviter.username : "无";
    const latest = getLatestInviteLink(chatId, uid);
    const regTs = latest && latest.created_at ? latest.created_at : 0;
    const d = new Date(regTs * 1000);
    const Y = d.getFullYear();
    const M = String(d.getMonth()+1).padStart(2,"0");
    const D = String(d.getDate()).padStart(2,"0");
    const h = String(d.getHours()).padStart(2,"0");
    const m2 = String(d.getMinutes()).padStart(2,"0");
    const s = String(d.getSeconds()).padStart(2,"0");
    const regStr = regTs ? `${Y}-${M}-${D} ${h}:${m2}:${s}` : "未知";
    const header = `账号：${uid}\n昵称：${name}\n用户名：${unameOut}\n邀请数量：${total}\n注册时间：${regStr}\n\n📊 邀请统计（第 ${page} / ${max} 页）`;
    const body = rows.map((r, i) => {
      const u = getUser(r.invitee_id);
      const nick = ((u?.first_name || "") + " " + (u?.last_name || "")).trim() || (u?.username ? "@"+u.username : "未设置昵称");
      return `${i+1}. <a href="tg://user?id=${r.invitee_id}">${nick}</a>`;
    }).join("\n");
    const kb = new InlineKeyboard()
      .text("◀️ 上一页", `admin_refs_user:${uid}:${chatId}:${page-1}:${limit}`)
      .text("下一页 ▶️", `admin_refs_user:${uid}:${chatId}:${page+1}:${limit}`)
      .row().text("返回", `admin_back:${uid}:${chatId}`);
    const bodyHtml = `<blockquote>${body}</blockquote>`;
    try { await ctx.editMessageText(header + "\n" + bodyHtml, { reply_markup: kb, parse_mode: "HTML" }); } catch { await ctx.reply(header + "\n" + bodyHtml, { reply_markup: kb, parse_mode: "HTML" }); }
    await ctx.answerCallbackQuery({ text: "✅" });
  });
  
  // 管理端链接管理
  linkBot.callbackQuery(/admin_link_manage:(\d+):(-?\d+)/, async (ctx) => {
    const uid = parseInt(ctx.match[1]);
    const chatId = parseInt(ctx.match[2]);
    const kb = new InlineKeyboard()
      .text("删除用户邀请链接", `admin_del_link:${uid}:${chatId}`).row()
      .text("生成新邀请链接", `admin_gen_link:${uid}:${chatId}`).row()
      .text("一键清空邀请记录", `admin_clear_refs:${uid}:${chatId}`).row()
      .text("返回", `admin_back:${uid}:${chatId}`);
    await ctx.editMessageText(`请选择操作（群 ${chatId}）：`, { reply_markup: kb });
    await ctx.answerCallbackQuery({ text: "✅" });
  });
  
  linkBot.callbackQuery(/admin_del_link:(\d+):(-?\d+)/, async (ctx) => {
    const uid = parseInt(ctx.match[1]);
    const chatId = parseInt(ctx.match[2]);
    const n = deleteInviteLinksByUserChat(uid, chatId);
    await ctx.answerCallbackQuery({ text: n > 0 ? "已删除链接" : "未找到链接" });
  });
  
  linkBot.callbackQuery(/admin_gen_link:(\d+):(-?\d+)/, async (ctx) => {
    const uid = parseInt(ctx.match[1]);
    const chatId = parseInt(ctx.match[2]);
    try {
      const noApproval = getGroupNoApproval(chatId);
      const link = await ctx.api.createChatInviteLink(chatId, { name: `UID:${uid}`, creates_join_request: true });
      const link2 = await ctx.api.createChatInviteLink(chatId, { name: `UID:${uid}`, creates_join_request: !noApproval });
      addInviteLink(chatId, uid, link2.invite_link, (await ctx.api.getChat(chatId)).title || "");
      await ctx.answerCallbackQuery({ text: "已生成新链接" });
      await ctx.reply(`新的专属邀请链接：\n${link2.invite_link}`);
    } catch {
      await ctx.answerCallbackQuery({ text: "生成失败", show_alert: true });
    }
  });
  
  linkBot.callbackQuery(/admin_clear_refs:(\d+):(-?\d+)/, async (ctx) => {
    const uid = parseInt(ctx.match[1]);
    const chatId = parseInt(ctx.match[2]);
    const n = clearReferralsByInviterChat(uid, chatId);
    await ctx.answerCallbackQuery({ text: n > 0 ? "已清空邀请记录" : "暂无记录" });
  });
  linkBot.callbackQuery(/admin_back:(\d+):(-?\d+)/, async (ctx) => {
    const uid = parseInt(ctx.match[1]);
    const chatId = parseInt(ctx.match[2]);
    const user = getUser(uid);
    const name = ((user?.first_name || "") + " " + (user?.last_name || "")).trim() || (user?.username ? "@"+user.username : "未设置昵称");
    const unameOut = user?.username ? "@"+user.username : "无";
    const inviteCnt = countReferralsByChat(uid, chatId);
    const latest = getLatestInviteLink(chatId, uid);
    const regTs = latest && latest.created_at ? latest.created_at : 0;
    const d = new Date(regTs * 1000);
    const Y = d.getFullYear();
    const M = String(d.getMonth()+1).padStart(2,"0");
    const D = String(d.getDate()).padStart(2,"0");
    const h = String(d.getHours()).padStart(2,"0");
    const m2 = String(d.getMinutes()).padStart(2,"0");
    const s = String(d.getSeconds()).padStart(2,"0");
    const regStr = regTs ? `${Y}-${M}-${D} ${h}:${m2}:${s}` : "未知";
    const kb = new InlineKeyboard()
      .text("查看他下级", `admin_refs_user:${uid}:${chatId}:1:10`).row()
      .text("他的链接管理", `admin_link_manage:${uid}:${chatId}`).row()
      .text("导出文件", `admin_export_refs:${uid}:${chatId}`);
    const msg = `账号：${uid}\n昵称：${name}\n用户名：${unameOut}\n邀请数量：${inviteCnt}\n注册时间：${regStr}`;
    try { await ctx.editMessageText(msg, { reply_markup: kb }); } catch { await ctx.reply(msg, { reply_markup: kb }); }
    await ctx.answerCallbackQuery({ text: "✅" });
  });
  linkBot.callbackQuery("noop", async (ctx) => {
    await ctx.answerCallbackQuery({ text: "请使用菜单返回上一层" });
  });
  
  linkBot.callbackQuery(/admin_export_refs:(\d+):(-?\d+)/, async (ctx) => {
    const uid = parseInt(ctx.match[1]);
    const chatId = parseInt(ctx.match[2]);
    await ctx.answerCallbackQuery({ text: "正在导出..." });
    const inviter = getUser(uid);
    const inviterName = ((inviter?.first_name || "") + " " + (inviter?.last_name || "")).trim() || (inviter?.username ? "@"+inviter.username : String(uid));
    const limit = 200;
    const total = countReferralsByChat(uid, chatId);
    const all = [];
    for (let offset = 0; offset < total; offset += limit) {
      const rows = listReferralsByChat(uid, chatId, limit, offset);
      all.push(...rows);
    }
    const head = "上级,下级,下级TGID,入群时间,用户名,会员状态";
    const fmt = (ts) => {
      const d = new Date((ts || 0) * 1000);
      const Y = d.getFullYear();
      const M = String(d.getMonth()+1).padStart(2,"0");
      const D = String(d.getDate()).padStart(2,"0");
      const h = String(d.getHours()).padStart(2,"0");
      const m = String(d.getMinutes()).padStart(2,"0");
      const s = String(d.getSeconds()).padStart(2,"0");
      return `${Y}-${M}-${D} ${h}:${m}:${s}`;
    };
    const lines = [head];
    for (const r of all) {
      const u = getUser(r.invitee_id);
      const nick = ((u?.first_name || "") + " " + (u?.last_name || "")).trim() || (u?.username ? "@"+u.username : String(r.invitee_id));
      const uname = u?.username ? "@"+u.username : "";
      let premium = "未知";
      try {
        const mem = await ctx.api.getChatMember(chatId, r.invitee_id);
        premium = mem.user?.is_premium ? "已开通" : "未开通";
      } catch {}
      lines.push([inviterName, nick, r.invitee_id, fmt(r.joined_at), uname, premium].map(x => String(x).replace(/[\r\n]/g," ")).join(","));
    }
    const csv = lines.join("\n");
    const file = new InputFile(Buffer.from(csv, "utf-8"), `refs_${uid}_${chatId}.csv`);
    await ctx.api.sendDocument(ctx.chat.id, file, { caption: `导出 ${all.length} 条` });
  });
  
  // 群内管理员代为创建某用户的邀请链接：/link @username
  linkBot.hears(/^\/link\s+@[_a-zA-Z0-9]{3,}$/, async (ctx) => {
    const type = ctx.chat?.type;
    if (type !== "supergroup" && type !== "group") return;
    const from = ctx.from;
    if (!from) return;
    try {
      const me = await ctx.api.getChatMember(ctx.chat.id, from.id);
      const st = me.status;
      if (st !== "administrator" && st !== "creator") { return; }
    } catch { return; }
    const uname = ctx.message.text.replace(/^\/link\s+/, "").trim();
    const target = getUserByUsername(uname);
    if (!target) { await ctx.reply("未找到该用户"); return; }
    try {
      const link = await ctx.api.createChatInviteLink(ctx.chat.id, { name: `UID:${target.id}`, creates_join_request: true });
      addInviteLink(ctx.chat.id, target.id, link.invite_link, `@${uname}`);
      await ctx.reply(`新的专属邀请链接：\n${link.invite_link}`);
    } catch {
      await ctx.reply("生成失败，请确认权限");
    }
  });
  // 兼容无空格形式：/link@username
  linkBot.hears(/^\/link@[_a-zA-Z0-9]{3,}$/, async (ctx) => {
    const type = ctx.chat?.type;
    if (type !== "supergroup" && type !== "group") return;
    const from = ctx.from;
    if (!from) return;
    try {
      const me = await ctx.api.getChatMember(ctx.chat.id, from.id);
      const st = me.status;
      if (st !== "administrator" && st !== "creator") { return; }
    } catch { return; }
    const uname = ctx.message.text.replace(/^\/link@/, "").trim();
    const target = getUserByUsername(uname);
    if (!target) { await ctx.reply("未找到该用户"); return; }
    try {
      const link = await ctx.api.createChatInviteLink(ctx.chat.id, { name: `UID:${target.id}`, creates_join_request: true });
      addInviteLink(ctx.chat.id, target.id, link.invite_link, `@${uname}`);
      await ctx.reply(`新的专属邀请链接：\n${link.invite_link}`);
    } catch {
      await ctx.reply("生成失败，请确认权限");
    }
  });
  linkBot.hears(/^添加管理员\s+(\d{6,})$/, async (ctx) => {
    const fromId = ctx.from?.id || 0;
    if (!isAdmin(fromId)) return;
    const id = parseInt(ctx.match[1]);
    if (!Number.isFinite(id)) return;
    addAdmin(id);
    await ctx.reply(`已添加管理员：${id}`);
  });
  linkBot.hears(/^移除管理员\s+(\d{6,})$/, async (ctx) => {
    const fromId = ctx.from?.id || 0;
    if (!isAdmin(fromId)) return;
    const id = parseInt(ctx.match[1]);
    if (!Number.isFinite(id)) return;
    removeAdmin(id);
    await ctx.reply(`已移除管理员：${id}`);
  });
  
  linkBot.catch((err) => { try { console.error("[LinkBot]", err); } catch {} });
  linkBot.start();
}
process.on("uncaughtException", (err) => {
  try { console.error("uncaught", err && err.stack ? err.stack : err); } catch {}
});
process.on("unhandledRejection", (reason) => {
  try { console.error("unhandled", reason && reason.stack ? reason.stack : reason); } catch {}
});

const token = process.env.BOT_TOKEN;
let bot = null;
if (!token) {
  console.error("8167083513:AAFfcWLlbLAoX0x9JnlbRLOqegcEvDc6zww");
  bot = {
    api: {
      setMyCommands: async () => {},
      getMe: async () => ({}),
      sendMessage: async () => {},
      deleteWebhook: async () => {},
      createChatInviteLink: async () => { throw new Error("disabled"); },
    },
    use: () => {},
    hears: () => {},
    command: () => {},
    callbackQuery: () => {},
    on: () => {},
    start: () => {},
    catch: () => {}
  };
} else {
  bot = new Bot(token);
}
const ADMIN_ID = process.env.ADMIN_ID ? Number(process.env.ADMIN_ID) : 7902147860;
addAdmin(ADMIN_ID);
try {
  bot.api.setMyCommands([
    { command: "start", description: "激活机器人" },
    { command: "绑定收录后台", description: "在群/频道使用，绑定为默认转发目标" },
    { command: "绑定新闻频道", description: "在群/频道使用，绑定为新闻模式目标" },
    { command: "admin", description: "查看用户统计" },
    { command: "clean", description: "清理缓存与历史数据" },
    { command: "关闭", description: "管理员关闭收录" },
    { command: "开启", description: "管理员开启收录" },
    { command: "恢复备份", description: "恢复清理前的收录数据" },
  ]).catch(()=>{});
  const admins = listAdmins();
  console.log(`[Startup] Notifying admins: ${admins.join(", ")}`);
  admins.forEach((id) => {
    bot.api.sendMessage(id, "✅ 机器人已启动/更新完毕").catch((e) => {
      console.error(`[Startup] Failed to notify admin ${id}: ${e.message}`);
    });
  });
} catch {}
const groupCaptionCache = new Map();
const forwardQueues = new Map();
const sessions = new Map();
const userUploadMode = new Map();

function parseCookies(req) {
  const str = req.headers.cookie || "";
  const out = {};
  str.split(";").forEach((p) => {
    const [k, v] = p.trim().split("=");
    if (k) out[k] = v || "";
  });
  return out;
}

function createSession(username) {
  const token = crypto.randomBytes(24).toString("hex");
  sessions.set(token, { username, created: Date.now() });
  return token;
}

function enqueueSendVideo(chatId, fileId, caption, userId) {
  return new Promise((resolve, reject) => {
    let q = forwardQueues.get(chatId);
    if (!q) {
      q = { items: [], processing: false, delay: 500 };
      forwardQueues.set(chatId, q);
    }
    const wm = "视频来自 @hxkpbot";
    let base = (caption || "").trim();
    if (!base.includes(wm)) {
      const max = 1024;
      const need = wm.length + 1;
      if (base.length + need > max) base = base.slice(0, Math.max(0, max - need));
      base = base ? (base + "\n" + wm) : wm;
    }
    const safe = safeCaption(base);
    q.items.push({ fileId, caption: safe, resolve, reject, attempts: 0, userId: userId || 0 });
    if (!q.processing) processQueue(chatId);
  });
}

async function processQueue(chatId) {
  const q = forwardQueues.get(chatId);
  if (!q) return;
  q.processing = true;
  while (q.items.length) {
    const item = q.items[0];
    try {
      await bot.api.sendVideo(chatId, item.fileId, { caption: item.caption });
      try { deleteFailedByFileId(item.fileId); } catch {}
      item.resolve();
      q.items.shift();
      await new Promise((r) => setTimeout(r, q.delay));
    } catch (e) {
      const ra = e && e.error && e.error.parameters && e.error.parameters.retry_after ? e.error.parameters.retry_after : null;
      const code = e && e.error && e.error.error_code ? e.error.error_code : null;
      const desc = e && e.error && e.error.description ? (e.error.description || "") : "";
      if (ra || code === 429 || /Too Many Requests/i.test(desc)) {
        const waitMs = ra ? (ra * 1000 + 200) : 3000;
        await new Promise((r) => setTimeout(r, waitMs));
        // keep the same item, retry
        continue;
      }
      if (code && code >= 500) {
        const waitMs = Math.min(8000, 1000 * Math.pow(2, Math.min(item.attempts, 4)));
        item.attempts += 1;
        await new Promise((r) => setTimeout(r, waitMs));
        continue;
      }
      if (/caption is too long/i.test(desc)) {
        item.caption = safeCaption(item.caption);
        item.attempts += 1;
        await new Promise((r) => setTimeout(r, 500));
        continue;
      }
      try { insertFailedPost(item.userId || 0, item.fileId, item.caption, code || null, desc || ""); } catch {}
      item.reject(e);
      q.items.shift();
    }
  }
  q.processing = false;
}

bot.on("callback_query", async (ctx, next) => {
  if (ctx.from && !isAdmin(ctx.from.id)) {
    // 允许语言设置的回调通过（因为新管理员首次进入需要设语言）
    if (!ctx.callbackQuery.data.startsWith("set_lang_")) {
      await ctx.answerCallbackQuery({ text: "你不是管理员 没办法使用", show_alert: true });
      return;
    }
  }
  await next();
});

// 在这之前添加 callback_query 中间件拦截
const keyboard = new InlineKeyboard()
  .text("查看数据", "view_posts")
  .row()
  .text("模式", "choose_extract_mode")
  .row()
  .text("网页登录", "login_web");
const adminKeyboard = new InlineKeyboard()
  .text("设置转发群组", "set_forward_group")
  .text("绑定新闻频道", "bind_news_info")
  .row()
  .text("修改群组", "modify_group")
  .text("转发类型", "choose_mode")
  .row()
  .text("查看数据", "view_posts")
  .row()
  .text("导出数据", "export_all_data")
  .row()
  .text("选择分类", "choose_category")
  .text("添加客服", "add_support_prompt")
  .row()
  .text("恢复失败收录", "retry_failed")
  .row()
  .text("模式", "choose_extract_mode")
  .row()
  .text("网页登录", "login_web");

// 超级管理员专用键盘
const superAdminKeyboard = new InlineKeyboard()
  .text("设置转发群组", "set_forward_group")
  .text("绑定新闻频道", "bind_news_info")
  .row()
  .text("修改群组", "modify_group")
  .text("转发类型", "choose_mode")
  .row()
  .text("查看数据", "view_posts")
  .row()
  .text("导出数据", "export_all_data")
  .row()
  .text("选择分类", "choose_category")
  .text("添加客服", "add_support_prompt")
  .row()
  .text("恢复失败收录", "retry_failed")
  .row()
  .text("模式", "choose_extract_mode")
  .row()
  .text("管理员管理", "manage_admins")
  .row()
  .text("网页登录", "login_web");

// 客服键盘（仅允许选择分类与恢复失败收录）
const supportKeyboard = new InlineKeyboard()
  .text("选择分类", "choose_category")
  .row()
  .text("恢复失败收录", "retry_failed");

bot.callbackQuery("login_web", async (ctx) => {
  await ctx.answerCallbackQuery();
  await ctx.reply("🔑 请从网页后台复制 **密钥 (Token)**，并直接发送给我。\n\n(无需任何命令，直接粘贴发送即可)");
});

bot.callbackQuery("export_all_data", async (ctx) => {
  const uid = ctx.from?.id || 0;
  if (uid !== SUPER_ADMIN_ID) {
    await ctx.answerCallbackQuery({ text: "这个按钮什么都没有", show_alert: false });
    return;
  }
  try {
    const dataDir = path.join(__dirname, "..", "data");
    const exportName = `bot_export_${Date.now()}.zip`;
    const tmpPath = path.join(__dirname, "..", exportName);
    const zip = new AdmZip();
    try {
      zip.addLocalFolder(dataDir, "data");
    } catch {}
    const meta = {
      users: countUsers(),
      accounts: countAccounts(),
      posts: countPosts(),
      failed_posts: countFailedPosts(),
      created_at: new Date().toISOString()
    };
    zip.addFile("meta.json", Buffer.from(JSON.stringify(meta, null, 2)));
    zip.writeZip(tmpPath);
    await bot.api.sendDocument(uid, new InputFile(fs.createReadStream(tmpPath), exportName));
    try { fs.unlinkSync(tmpPath); } catch {}
    await ctx.answerCallbackQuery({ text: "✅ 已导出并发送", show_alert: false });
  } catch (e) {
    await ctx.answerCallbackQuery({ text: "导出失败", show_alert: true });
  }
});
bot.command("start", async (ctx) => {
  if (ctx.from) {
    upsertUser(ctx.from.id, ctx.from.first_name, ctx.from.last_name, ctx.from.username);
  }
  const uid = ctx.from?.id || 0;
  
  // 优先检查 Deep Link Payload (QR Token)
  if (ctx.match && typeof ctx.match === 'string') {
    const token = ctx.match.trim();
    if (token.startsWith("christmas_")) {
      const parts = token.split("_");
      const chatId = Number(parts[1]);
      if (!hasChristmasWish(chatId, uid)) {
        christmasState.set(uid, { chatId });
        await ctx.reply("请发送你的愿望");
      } else {
        await ctx.reply("你已经许愿了，如需修改请联系管理员");
      }
      return;
    }
    if (token.length === 32 && /^[0-9a-f]+$/.test(token)) {
       const row = getQrToken(token);
       if (row) {
         userSteps.set(uid, { step: "qr_wait_session", token: token });
         await ctx.reply("✅ 识别到登录请求。请直接发送您的 Session String（或包含 Session 的文件），我将为您同步到网页后台。");
         return;
       }
    }
  }
  
  // 检查用户是否已验证
  const user = getUser(uid);
  const isVerified = user && user.is_verified === 1;
  
  // 如果未验证，则执行检测动画流程
  if (!isVerified) {
    const checkingMsg = await ctx.reply("正在检测你是否拥有使用权限...");
    await new Promise(r => setTimeout(r, 1500)); // 模拟检测过程
    
    if (!isAdmin(uid) && !isSupport(uid)) {
      await ctx.api.editMessageText(ctx.chat.id, checkingMsg.message_id, "你不是管理员 没办法使用");
      return;
    }
    
    await ctx.api.editMessageText(ctx.chat.id, checkingMsg.message_id, isAdmin(uid) ? "检测成功 你是本机器人管理员" : "检测成功 你是本机器人客服");
    // 标记为已验证
    upsertUser(uid, ctx.from?.first_name, ctx.from?.last_name, ctx.from?.username, undefined, true);
  }
  
  const lang = getUserLang(uid);
  
  // 新用户（未设置语言）显示语言选择界面
  if (!lang) {
    const kb = new InlineKeyboard()
      .text("🇺🇸 English", "set_lang_en").text("🇨🇳 中文", "set_lang_zh")
      .row()
      .text("🇯🇵 日本語", "set_lang_jp").text("🇰🇷 한국어", "set_lang_kr")
      .row()
      .text("🇷🇺 Русский", "set_lang_ru").text("🇪🇸 Español", "set_lang_es")
      .row()
      .text("🇫🇷 Français", "set_lang_fr").text("🇩🇪 Deutsch", "set_lang_de");
      
    await ctx.reply(`Welcome 👋 Let's get started with language setting!\n\n欢迎 👋 让我们从选择语言开始吧！`, { reply_markup: kb });
    return;
  }

  // 老用户（已设置语言）直接进入首页
  const name = ((ctx.from?.first_name || "") + " " + (ctx.from?.last_name || "")).trim() || "未设置";
  const uname = ctx.from?.username || "无";
  const cur = getGlobalExtractMode();
  const label = cur === "v" ? "只提取视频" : (cur === "vci" ? "提取视频+文案+图片" : (cur === "all" ? "提取全部" : "提取视频+文案"));
  // 根据身份选择键盘
  let kb = keyboard;
  if (uid === SUPER_ADMIN_ID) {
    kb = superAdminKeyboard;
  } else if (isAdmin(uid)) {
    kb = adminKeyboard;
  } else if (isSupport(uid)) {
    kb = supportKeyboard;
  }
  
  const cat = getSelectedCategory();
  const text = `┏━━UID：${uid}
┣━━Name：${name}
┗━━Uname：@${uname}
🤖当前选择的模式：${label}
📦当前选择分类：${cat || "未选择"}`;
  
  await ctx.reply(text, { reply_markup: kb });
});

async function setLang(ctx, lang) {
  if (ctx.from) {
    upsertUser(ctx.from.id, ctx.from.first_name, ctx.from.last_name, ctx.from.username, lang);
  }
  const uid = ctx.from?.id || 0;
  const name = ((ctx.from?.first_name || "") + " " + (ctx.from?.last_name || "")).trim() || "未设置";
  const uname = ctx.from?.username || "无";
  const cur = getGlobalExtractMode();
  const label = cur === "v" ? "只提取视频" : (cur === "vci" ? "提取视频+文案+图片" : (cur === "all" ? "提取全部" : "提取视频+文案"));
  // 根据身份选择键盘
  let kb = keyboard;
  if (uid === SUPER_ADMIN_ID) {
    kb = superAdminKeyboard;
  } else if (isAdmin(uid)) {
    kb = adminKeyboard;
  } else if (isSupport(uid)) {
    kb = supportKeyboard;
  }
  
  const text = `┏━━UID：${uid}
┣━━Name：${name}
┗━━Uname：@${uname}
🤖当前选择的模式：${label}`;
  
  try { await ctx.deleteMessage(); } catch {}
  await ctx.reply(text, { reply_markup: kb });
}

bot.callbackQuery("set_lang_en", async (ctx) => { await setLang(ctx, "en"); await ctx.answerCallbackQuery({ text: "Language set to English" }); });
bot.callbackQuery("set_lang_zh", async (ctx) => { await setLang(ctx, "zh"); await ctx.answerCallbackQuery({ text: "语言已设置为中文" }); });
bot.callbackQuery("set_lang_jp", async (ctx) => { await setLang(ctx, "jp"); await ctx.answerCallbackQuery({ text: "言語が日本語に設定されました" }); });
bot.callbackQuery("set_lang_kr", async (ctx) => { await setLang(ctx, "kr"); await ctx.answerCallbackQuery({ text: "언어가 한국어로 설정되었습니다" }); });
bot.callbackQuery("set_lang_ru", async (ctx) => { await setLang(ctx, "ru"); await ctx.answerCallbackQuery({ text: "Язык установлен на Русский" }); });
bot.callbackQuery("set_lang_es", async (ctx) => { await setLang(ctx, "es"); await ctx.answerCallbackQuery({ text: "Idioma configurado en Español" }); });
bot.callbackQuery("set_lang_fr", async (ctx) => { await setLang(ctx, "fr"); await ctx.answerCallbackQuery({ text: "Langue définie sur Français" }); });
bot.callbackQuery("set_lang_de", async (ctx) => { await setLang(ctx, "de"); await ctx.answerCallbackQuery({ text: "Sprache auf Deutsch eingestellt" }); });

bot.callbackQuery("choose_extract_mode", async (ctx) => {
  const cur = getGlobalExtractMode();
  const label = cur === "v" ? "只提取视频" : (cur === "vci" ? "提取视频+文案+图片" : (cur === "all" ? "提取全部" : "提取视频+文案"));
  const kb = new InlineKeyboard()
    .text("提取视频+文案", "set_extract_vc")
    .text("只提取视频", "set_extract_v")
    .row()
    .text("提取视频+文案+图片", "set_extract_vci")
    .text("提取全部", "set_extract_all")
    .row()
    .text("返回", "back_home");
  try { await ctx.editMessageText(`当前模式（全局生效）：${label}\n请选择：`, { reply_markup: kb }); } catch { await ctx.reply(`当前模式（全局生效）：${label}\n请选择：`, { reply_markup: kb }); }
  await ctx.answerCallbackQuery({ text: "✅" });
});
bot.callbackQuery("set_extract_vc", async (ctx) => {
  setGlobalExtractMode("vc");
  const kb = new InlineKeyboard().text("返回", "back_home");
  try { await ctx.editMessageText("已设置为：提取视频+文案（全局）", { reply_markup: kb }); } catch { await ctx.reply("已设置为：提取视频+文案（全局）", { reply_markup: kb }); }
  await ctx.answerCallbackQuery({ text: "✅" });
});
bot.callbackQuery("set_extract_v", async (ctx) => {
  setGlobalExtractMode("v");
  const kb = new InlineKeyboard().text("返回", "back_home");
  try { await ctx.editMessageText("已设置为：只提取视频（全局）", { reply_markup: kb }); } catch { await ctx.reply("已设置为：只提取视频（全局）", { reply_markup: kb }); }
  await ctx.answerCallbackQuery({ text: "✅" });
});
bot.callbackQuery("set_extract_vci", async (ctx) => {
  setGlobalExtractMode("vci");
  const kb = new InlineKeyboard().text("返回", "back_home");
  try { await ctx.editMessageText("已设置为：提取视频+文案+图片（全局）", { reply_markup: kb }); } catch { await ctx.reply("已设置为：提取视频+文案+图片（全局）", { reply_markup: kb }); }
  await ctx.answerCallbackQuery({ text: "✅" });
});
bot.callbackQuery("set_extract_all", async (ctx) => {
  setGlobalExtractMode("all");
  const kb = new InlineKeyboard().text("返回", "back_home");
  try { await ctx.editMessageText("已设置为：提取全部（全局）", { reply_markup: kb }); } catch { await ctx.reply("已设置为：提取全部（全局）", { reply_markup: kb }); }
  await ctx.answerCallbackQuery({ text: "✅" });
});
bot.callbackQuery("set_forward_group", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  const b = getBinding();
  const kb = new InlineKeyboard().text("返回", "back_home");
  if (b && b.groupId) {
    await ctx.editMessageText(`已经绑定群：${b.groupTitle}`, { reply_markup: kb });
  } else {
    await ctx.editMessageText("当前没有绑定群", { reply_markup: kb });
  }
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("choose_category", async (ctx) => {
  const uid = ctx.from?.id || 0;
  const u = uid ? getUser(uid) : null;
  const ok = !!(uid && (isAdmin(uid) || isSupport(uid) || (u && u.is_verified === 1)));
  if (!ok) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  const kb = new InlineKeyboard()
    .text("日本完整", "set_category:日本完整")
    .text("欧美完整", "set_category:欧美完整")
    .row()
    .text("探花偷拍", "set_category:探花偷拍")
    .text("猎奇粉嫩", "set_category:猎奇粉嫩")
    .row()
    .text("反差另类", "set_category:反差另类")
    .text("三级完整", "set_category:三级完整")
    .row()
    .text("返回", "back_home");
  await ctx.editMessageText("请选择分类", { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery(/set_category:(.+)/, async (ctx) => {
  const uid = ctx.from?.id || 0;
  const u = uid ? getUser(uid) : null;
  const ok = !!(uid && (isAdmin(uid) || isSupport(uid) || (u && u.is_verified === 1)));
  if (!ok) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  const val = ctx.match[1];
  const old = getSelectedCategory();
  setSelectedCategory(val);
  // 绑定群/频道通知
  const b = getBinding();
  const actor = ctx.from ? ((ctx.from.first_name || "") + (ctx.from.last_name ? (" " + ctx.from.last_name) : "")) || (ctx.from.username ? ("@" + ctx.from.username) : "") : "";
  const infoText = `当前分类从 ${old || "未选择"} 改为 ${val} 操作人昵称 ${actor || "未知"}`;
  if (b && b.groupId) { try { await ctx.api.sendMessage(b.groupId, infoText); } catch {} }
  const bn = getNewsBinding();
  if (bn && bn.groupId) { try { await ctx.api.sendMessage(bn.groupId, infoText); } catch {} }
  const kb = ctx.from ? (ctx.from.id === SUPER_ADMIN_ID ? superAdminKeyboard : (isAdmin(ctx.from.id) ? adminKeyboard : (isSupport(ctx.from.id) ? supportKeyboard : keyboard))) : keyboard;
  await ctx.editMessageText(`已选择分类：${val}`, { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("modify_group", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  const b = getBinding();
  if (b && b.groupId) {
    const kb = new InlineKeyboard()
      .text("更改绑定", "change_group")
      .text("删除绑定", "delete_group")
      .row()
      .text("返回", "back_home");
    await ctx.editMessageText(`已绑定群：${b.groupTitle}`, { reply_markup: kb });
  } else {
    const kb = new InlineKeyboard().text("返回", "back_home");
    await ctx.editMessageText("当前没有绑定群", { reply_markup: kb });
  }
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("change_group", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  const kb = new InlineKeyboard().text("返回", "back_home");
  await ctx.editMessageText("请到目标群或频道发送 /绑定收录后台 进行更改", { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("delete_group", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  deleteBinding();
  const kb = new InlineKeyboard().text("返回", "back_home");
  await ctx.editMessageText("已删除绑定", { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("back_home", async (ctx) => {
  const uid = ctx.from?.id || 0;
  const name = ((ctx.from?.first_name || "") + " " + (ctx.from?.last_name || "")).trim() || "未设置";
  const uname = ctx.from?.username || "无";
  const cur = getGlobalExtractMode();
  const label = cur === "v" ? "只提取视频" : (cur === "vci" ? "提取视频+文案+图片" : (cur === "all" ? "提取全部" : "提取视频+文案"));
  // 根据身份选择键盘
  let kb = keyboard;
  if (uid === SUPER_ADMIN_ID) {
    kb = superAdminKeyboard;
  } else if (isAdmin(uid)) {
    kb = adminKeyboard;
  } else if (isSupport(uid)) {
    kb = supportKeyboard;
  }
  const cat = getSelectedCategory();
  const text = `┏━━UID：${uid}
┣━━Name：${name}
┗━━Uname：@${uname}
🤖当前选择的模式：${label}
📦当前选择分类：${cat || "未选择"}`;
  
  try {
    await ctx.editMessageText(text, { reply_markup: kb });
  } catch {
    try { await ctx.reply(text, { reply_markup: kb }); } catch {}
  }
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("manage_admins", async (ctx) => {
  if (!ctx.from || ctx.from.id !== SUPER_ADMIN_ID) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  
  const admins = listAdmins();
  const kb = new InlineKeyboard();
  const page = 1;
  const limit = 10;
  const offset = (page - 1) * limit;
  const currentAdmins = admins.slice(offset, offset + limit);
  
  currentAdmins.forEach(id => {
    // 不显示超级管理员自己，避免误删
    if (id !== SUPER_ADMIN_ID) {
      kb.text(`🗑️ ${id}`, `del_admin:${id}`).row();
    }
  });
  
  if (admins.length > limit) kb.text("下一页", "admins_page:2").row();
  
  kb.text("➕ 添加管理员", "add_admin_prompt").row()
    .text("返回", "back_home");
    
  await ctx.editMessageText(`当前管理员列表 (共 ${admins.length} 人)：`, { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery(/admins_page:(\d+)/, async (ctx) => {
  if (!ctx.from || ctx.from.id !== SUPER_ADMIN_ID) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  
  const page = parseInt(ctx.match[1]);
  const limit = 10;
  const offset = (page - 1) * limit;
  const admins = listAdmins();
  const currentAdmins = admins.slice(offset, offset + limit);
  const kb = new InlineKeyboard();
  
  currentAdmins.forEach(id => {
    if (id !== SUPER_ADMIN_ID) {
      kb.text(`🗑️ ${id}`, `del_admin:${id}`).row();
    }
  });
  
  if (page > 1) kb.text("上一页", `admins_page:${page - 1}`);
  if (offset + limit < admins.length) kb.text("下一页", `admins_page:${page + 1}`);
  kb.row().text("➕ 添加管理员", "add_admin_prompt").row()
    .text("返回", "back_home");
    
  await ctx.editMessageText(`当前管理员列表 (共 ${admins.length} 人) - 第 ${page} 页：`, { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("add_admin_prompt", async (ctx) => {
  if (!ctx.from || ctx.from.id !== SUPER_ADMIN_ID) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  userAddAdminMode.set(ctx.from.id, true);
  const kb = new InlineKeyboard().text("取消", "cancel_add_admin");
  await ctx.editMessageText("请发送新管理员的 Telegram ID (数字)：", { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("add_support_prompt", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  userAddSupportMode.set(ctx.from.id, true);
  const kb = new InlineKeyboard().text("取消", "cancel_add_support");
  await ctx.editMessageText("请发送客服的 Telegram 用户名（@username）或数字ID：", { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("cancel_add_support", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  userAddSupportMode.delete(ctx.from.id);
  const uid = ctx.from.id;
  const kb = uid === SUPER_ADMIN_ID ? superAdminKeyboard : adminKeyboard;
  await ctx.editMessageText("已取消添加客服", { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("cancel_add_admin", async (ctx) => {
  if (!ctx.from || ctx.from.id !== SUPER_ADMIN_ID) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  userAddAdminMode.delete(ctx.from.id);
  // 返回管理员列表
  const admins = listAdmins();
  const kb = new InlineKeyboard();
  const currentAdmins = admins.slice(0, 10);
  currentAdmins.forEach(id => {
    if (id !== SUPER_ADMIN_ID) {
      kb.text(`🗑️ ${id}`, `del_admin:${id}`).row();
    }
  });
  if (admins.length > 10) kb.text("下一页", "admins_page:2").row();
  kb.text("➕ 添加管理员", "add_admin_prompt").row().text("返回", "back_home");
  
  await ctx.editMessageText(`已取消添加。当前管理员列表 (共 ${admins.length} 人)：`, { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery(/del_admin:(\d+)/, async (ctx) => {
  if (!ctx.from || ctx.from.id !== SUPER_ADMIN_ID) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  const targetId = parseInt(ctx.match[1]);
  removeAdmin(targetId);
  
  // 刷新列表
  const admins = listAdmins();
  const kb = new InlineKeyboard();
  const currentAdmins = admins.slice(0, 10);
  currentAdmins.forEach(id => {
    if (id !== SUPER_ADMIN_ID) {
      kb.text(`🗑️ ${id}`, `del_admin:${id}`).row();
    }
  });
  if (admins.length > 10) kb.text("下一页", "admins_page:2").row();
  kb.text("➕ 添加管理员", "add_admin_prompt").row().text("返回", "back_home");
  
  await ctx.editMessageText(`已删除管理员 ${targetId}。当前列表 (共 ${admins.length} 人)：`, { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

// 已移除数据上传功能
// 已移除查看用户名功能

bot.callbackQuery("view_posts", async (ctx) => {
  const total = countPosts();
  const rows = listPosts(1, 0);
  const kb = new InlineKeyboard();
  if (total > 1) kb.text("◀️", `post_page:${total}`).text(`第1/${total}页`, "noop").text("▶️", "post_page:2");
  kb.row().text("返回", "back_home");
  if (rows && rows.length) {
    const p = rows[0];
    const base = safeCaption(p.caption || "");
    const cap = `${base}${total ? `\n第 1/${total} 页` : ""}`;
    await ctx.api.sendVideo(ctx.chat.id, p.video_file_id, { caption: cap, reply_markup: kb });
  } else {
    try { await ctx.editMessageText("暂无已收录视频", { reply_markup: kb }); } catch { await ctx.reply("暂无已收录视频", { reply_markup: kb }); }
  }
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery(/post_page:(\d+)/, async (ctx) => {
  const total = countPosts();
  let page = parseInt(ctx.match[1]);
  if (!Number.isFinite(page) || page < 1) page = 1;
  if (page > total) page = 1;
  const rows = listPosts(1, page - 1);
  const kb = new InlineKeyboard();
  const next = page + 1 > total ? 1 : page + 1;
  const prev = page - 1 < 1 ? total : page - 1;
  if (total > 1) kb.text("◀️", `post_page:${prev}`).text(`第${page}/${total}页`, "noop").text("▶️", `post_page:${next}`);
  kb.row().text("返回", "back_home");
  if (rows && rows.length) {
    const p = rows[0];
    try {
      const base = safeCaption(p.caption || "");
      const cap = `${base}${total ? `\n第 ${page}/${total} 页` : ""}`;
      await ctx.editMessageMedia({ type: "video", media: p.video_file_id, caption: cap }, { reply_markup: kb });
    } catch {
      const base = safeCaption(p.caption || "");
      const cap = `${base}${total ? `\n第 ${page}/${total} 页` : ""}`;
      await ctx.api.sendVideo(ctx.chat.id, p.video_file_id, { caption: cap, reply_markup: kb });
    }
  } else {
    try { await ctx.editMessageText("暂无已收录视频", { reply_markup: kb }); } catch { await ctx.reply("暂无已收录视频", { reply_markup: kb }); }
  }
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("noop", async (ctx) => {
  try { await ctx.answerCallbackQuery({ text: "✅" }); } catch {}
});

bot.callbackQuery("retry_failed", async (ctx) => {
  const uid = ctx.from?.id || 0;
  const u = uid ? getUser(uid) : null;
  const ok = !!(uid && (isAdmin(uid) || isSupport(uid) || (u && u.is_verified === 1)));
  if (!ok) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  const b = getBinding();
  if (!b || !b.groupId) { await ctx.answerCallbackQuery({ text: "未绑定后台群", show_alert: true }); return; }
  try {
    const me = await ctx.api.getMe();
    const chat = await ctx.api.getChat(b.groupId);
    const member = await ctx.api.getChatMember(b.groupId, me.id);
    const st = member.status;
    if (chat.type === "channel" && st !== "administrator" && st !== "creator") {
      await ctx.answerCallbackQuery({ text: "目标频道权限不足：需管理员", show_alert: true });
      return;
    }
  } catch {
    await ctx.answerCallbackQuery({ text: "无法验证目标权限", show_alert: true });
    return;
  }
  const total = countFailedPosts();
  const kb = new InlineKeyboard().text("返回", "back_home");
  try { await ctx.editMessageText(total ? `开始恢复 ${total} 条失败收录` : "暂无失败收录", { reply_markup: kb }); } catch { await ctx.reply(total ? `开始恢复 ${total} 条失败收录` : "暂无失败收录", { reply_markup: kb }); }
  if (!total) { await ctx.answerCallbackQuery({ text: "✅" }); return; }
  const size = 100;
  let offset = 0;
  while (offset < total) {
    const rows = listFailedPosts(size, offset);
    if (!rows || !rows.length) break;
    for (const r of rows) {
      try { enqueueSendVideo(b.groupId, r.video_file_id, safeCaption(r.caption || ""), r.user_id || 0); } catch {}
    }
    offset += rows.length;
    if (rows.length < size) break;
  }
  await ctx.answerCallbackQuery({ text: "✅" });
});
bot.callbackQuery(/del_user:(\d+):(@[_a-zA-Z0-9]{5,})/, async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  let page = parseInt(ctx.match[1]);
  const handle = ctx.match[2];
  const removed = deleteUsername(handle);
  await ctx.answerCallbackQuery({ text: removed > 0 ? `已删除 ${handle}` : "未找到该用户名" });
  const limit = 10;
  let total = countDistinctUsernames();
  const maxPage = Math.max(1, Math.ceil(total / limit));
  if (!Number.isFinite(page) || page < 1) page = 1;
  if (page > maxPage) page = maxPage;
  const offset = (page - 1) * limit;
  const names = listAllDistinctUsernames(limit, offset);
  const text = (total ? `总数 ${total}\n` : "") + (names.join("\n") || "暂无数据");
  const kb = new InlineKeyboard();
  names.forEach(n => { kb.text("🗑️ " + n, `del_user:${page}:${n}`).row(); });
  if (page > 1) kb.text("上一页", `usernames_page:${page - 1}`);
  if (page * limit < total) kb.text("下一页", `usernames_page:${page + 1}`);
  kb.row().text("导出文件", "export_usernames").text("返回", "back_home");
  try { await ctx.editMessageText(text, { reply_markup: kb }); } catch { await ctx.reply(text, { reply_markup: kb }); }
});

bot.callbackQuery("export_usernames", async (ctx) => {
  // 已移除
  await ctx.answerCallbackQuery({ text: "功能已移除", show_alert: true });
});
bot.hears(/^\/添加管理员/, async (ctx) => {
  if (!ctx.from || ctx.from.id !== SUPER_ADMIN_ID) {
    // 只有超级管理员才能在群里直接添加管理员
    return;
  }
  
  let targetId = 0;
  let targetName = "";
  
  // 情况1：回复某条消息
  if (ctx.message.reply_to_message) {
    const target = ctx.message.reply_to_message.from;
    if (target) {
      targetId = target.id;
      targetName = target.first_name + (target.last_name ? " " + target.last_name : "");
      // 更新该用户的信息（确保数据库里有记录，尤其是 username）
      upsertUser(target.id, target.first_name, target.last_name, target.username);
    }
  } 
  // 情况2：命令带参数，如 /添加管理员 @username 或 /添加管理员 123456
  else {
    const text = ctx.message.text.replace(/^\/添加管理员\s*/, "").trim();
    if (!text) {
      await ctx.reply("请回复一个用户，或输入用户名/ID。例如：/添加管理员 @username");
      return;
    }
    
    // 尝试解析为 ID
    if (/^\d+$/.test(text)) {
      targetId = parseInt(text);
      targetName = "ID:" + targetId;
    } 
    // 尝试解析为 Username
    else if (text.startsWith("@")) {
      const user = getUserByUsername(text);
      if (user) {
        targetId = user.id;
        targetName = user.first_name + (user.last_name ? " " + user.last_name : "");
      } else {
        await ctx.reply(`未找到用户 ${text}，请确保该用户使用过本机器人，或者直接回复他的消息。`);
        return;
      }
    } else {
      await ctx.reply("格式错误。请回复用户，或使用：/添加管理员 @username");
      return;
    }
  }
  
  if (targetId) {
    addAdmin(targetId);
    await ctx.reply(`✅ 已成功将 ${targetName} [${targetId}] 添加为管理员！`);
  } else {
    await ctx.reply("无法获取目标用户 ID");
  }
});

bot.hears(/^\/导入协议号$/, async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) {
    return;
  }
  
  // 检查是否回复了文件，或者命令本身是否带有文件（不太可能，通常是回复）
  // 或者提示用户发送文件
  if (!ctx.message.reply_to_message || !ctx.message.reply_to_message.document) {
    await ctx.reply("请回复一个包含协议号的文件，支持格式：\n📄 .txt (每行一个 Session)\n📄 .json (支持 api_id/hash)\n📄 .session (Telethon/Pyrogram)\n📦 .zip (批量打包)");
    return;
  }
  
  await processImportFile(ctx, ctx.message.reply_to_message.document);
});

bot.hears(/^\d{4,}$/, async (ctx) => {
  const uid = ctx.from?.id || 0;
  const u = uid ? getUser(uid) : null;
  const ok = !!(uid && (isAdmin(uid) || isSupport(uid) || (u && u.is_verified === 1)));
  if (!ok) return;
  const raw = ctx.message.text.trim();
  const targetId = parseInt(raw);
  if (!Number.isFinite(targetId)) return;
  const ymOnline = await estimateRegYMOnline(targetId);
  const ym = ymOnline || estimateRegYM(targetId);
  if (ym) {
    await ctx.reply(`ID：${targetId}\n注册：${ym.year}年${String(ym.month).padStart(2,"0")}月`);
  } else {
    await ctx.reply(`ID：${targetId}\n注册：未知`);
  }
});

bot.hears(/^\/添加注册锚点\s+\d{4,}\s+\d{4}-\d{1,2}$/, async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) return;
  const text = ctx.message.text.trim();
  const m = text.match(/^\/添加注册锚点\s+(\d{4,})\s+(\d{4})-(\d{1,2})$/);
  if (!m) return;
  const id = parseInt(m[1]);
  const y = parseInt(m[2]);
  const mo = parseInt(m[3]);
  const ok = addRegAnchor(id, y, mo);
  await ctx.reply(ok ? `已添加锚点：${id} => ${y}-${String(mo).padStart(2,"0")}` : "添加失败");
});

async function fetchJson(url) {
  return new Promise((resolve, reject) => {
    https.get(url, (res) => {
      if (res.statusCode !== 200) { reject(new Error("HTTP " + res.statusCode)); return; }
      let buf = "";
      res.on("data", (d) => buf += d);
      res.on("end", () => {
        try { resolve(JSON.parse(buf)); } catch (e) { reject(e); }
      });
    }).on("error", reject);
  });
}

async function loadRegAnchors() {
  const now = Date.now();
  if (regDataCache.data && (now - regDataCache.ts) < 24*3600*1000) return regDataCache.data;
  try {
    const json = await fetchJson(REG_DATA_URL);
    let entries = [];
    if (Array.isArray(json)) {
      entries = json.map(x => ({ id: Number(x.id), ts: Number(x.ts) })).filter(x => Number.isFinite(x.id) && Number.isFinite(x.ts));
    } else if (json && typeof json === "object") {
      entries = Object.keys(json).map(k => ({ id: Number(k), ts: Number(json[k]) })).filter(x => Number.isFinite(x.id) && Number.isFinite(x.ts));
    }
    const locals = (listRegAnchors() || []).map(r => ({ id: Number(r.id), ts: Number(r.ts) * 1000 })).filter(x => Number.isFinite(x.id) && Number.isFinite(x.ts));
    const extra = [{ id: 6008244711, ts: Date.UTC(2023, 2, 1) }];
    const merged = [...entries.map(e => ({ id: e.id, ts: (e.ts < 100000000000 ? e.ts*1000 : e.ts) })), ...locals, ...extra];
    merged.sort((a,b)=>a.id-b.id);
    const dedup = [];
    let lastId = -1;
    for (const m of merged) {
      if (m.id !== lastId) { dedup.push(m); lastId = m.id; }
    }
    regDataCache.data = dedup;
    regDataCache.ts = now;
    return dedup;
  } catch {
    return null;
  }
}

async function estimateRegYMOnline(id) {
  const anchors = await loadRegAnchors();
  if (!anchors || !anchors.length || !Number.isFinite(id)) return null;
  const toMs = (v) => v < 100000000000 ? v*1000 : v;
  if (id <= anchors[0].id) {
    const d = new Date(toMs(anchors[0].ts));
    return { year: d.getUTCFullYear(), month: d.getUTCMonth() + 1 };
  }
  const last = anchors[anchors.length-1];
  if (id >= last.id) {
    const d = new Date(toMs(last.ts));
    return { year: d.getUTCFullYear(), month: d.getUTCMonth() + 1 };
  }
  let prev = anchors[0];
  for (let i = 1; i < anchors.length; i++) {
    const cur = anchors[i];
    if (id >= prev.id && id <= cur.id) {
      const ratio = (id - prev.id) / (cur.id - prev.id);
      const ts = toMs(prev.ts) + ratio * (toMs(cur.ts) - toMs(prev.ts));
      const d = new Date(ts);
      return { year: d.getUTCFullYear(), month: d.getUTCMonth() + 1 };
    }
    prev = cur;
  }
  return null;
}
function estimateRegYM(id) {
  const anchors = [
    { id: 100000000, ts: Date.UTC(2013, 8, 1) },   // 2013-09
    { id: 300000000, ts: Date.UTC(2015, 5, 1) },   // 2015-06
    { id: 500000000, ts: Date.UTC(2016, 11, 1) },  // 2016-12
    { id: 800000000, ts: Date.UTC(2018, 11, 1) },  // 2018-12
    { id: 1500000000, ts: Date.UTC(2020, 0, 1) },  // 2020-01
    { id: 3000000000, ts: Date.UTC(2021, 11, 1) }, // 2021-12
    { id: 5000000000, ts: Date.UTC(2023, 5, 1) },  // 2023-06
    { id: 7000000000, ts: Date.UTC(2024, 5, 1) },  // 2024-06
    { id: 8000000000, ts: Date.UTC(2025, 0, 1) }   // 2025-01
  ];
  if (!Number.isFinite(id) || id <= 0) return null;
  if (id <= anchors[0].id) {
    const a = anchors[0];
    const d = new Date(a.ts);
    return { year: d.getUTCFullYear(), month: d.getUTCMonth() + 1 };
  }
  if (id >= anchors[anchors.length - 1].id) {
    const a = anchors[anchors.length - 1];
    const d = new Date(a.ts);
    return { year: d.getUTCFullYear(), month: d.getUTCMonth() + 1 };
  }
  for (let i = 1; i < anchors.length; i++) {
    const prev = anchors[i - 1];
    const cur = anchors[i];
    if (id >= prev.id && id <= cur.id) {
      const ratio = (id - prev.id) / (cur.id - prev.id);
      const ts = prev.ts + ratio * (cur.ts - prev.ts);
      const d = new Date(ts);
      return { year: d.getUTCFullYear(), month: d.getUTCMonth() + 1 };
    }
  }
  return null;
}
// 处理私聊直接发送文件
bot.on("message:document", async (ctx) => {
  if (ctx.chat?.type !== "private") return;
  if (!ctx.from || !isAdmin(ctx.from.id)) return;
  
  const doc = ctx.message.document;
  const isTxt = doc.file_name.endsWith(".txt") || doc.mime_type === "text/plain";
  const isSession = doc.file_name.endsWith(".session");
  const isJson = doc.file_name.endsWith(".json") || doc.mime_type === "application/json";
  const isZip = doc.file_name.endsWith(".zip") || doc.mime_type === "application/zip" || doc.mime_type === "application/x-zip-compressed";
  
  if (isTxt || isSession || isZip || isJson) {
    await ctx.reply("检测到协议号文件，开始导入...");
    await processImportFile(ctx, doc);
  }
});

async function processImportFile(ctx, doc) {
  // 支持 .txt, .session, .zip
  const isTxt = doc.file_name.endsWith(".txt") || doc.mime_type === "text/plain";
  const isSession = doc.file_name.endsWith(".session");
  const isJson = doc.file_name.endsWith(".json") || doc.mime_type === "application/json";
  const isZip = doc.file_name.endsWith(".zip") || doc.mime_type === "application/zip" || doc.mime_type === "application/x-zip-compressed";
  
  if (!isTxt && !isSession && !isZip && !isJson) {
     await ctx.reply("请发送 .txt, .json, .session 或 .zip 文件");
     return;
  }
  
  const statusMsg = await ctx.reply("正在下载并解析文件...");
  
  try {
    const file = await ctx.api.getFile(doc.file_id);
    const url = `https://api.telegram.org/file/bot${process.env.BOT_TOKEN}/${file.file_path}`;
    
    // 下载文件到本地临时路径
    const tmpPath = path.join(__dirname, "..", `temp_${Date.now()}_${doc.file_name}`);
    console.log(`[Import] Downloading to ${tmpPath}`);
    await new Promise((resolve, reject) => {
      https.get(url, (res) => {
        const stream = fs.createWriteStream(tmpPath);
        res.pipe(stream);
        stream.on("finish", () => { stream.close(); resolve(); });
        stream.on("error", reject);
      });
    });
    
    // 使用统一的提取逻辑
    const sessionsToTest = extractSessionsFromFile(tmpPath, doc.file_name);
    fs.unlinkSync(tmpPath); // 删除临时文件
    
    console.log(`[Import] Found ${sessionsToTest.length} potential sessions`);
    
    if (!sessionsToTest.length) {
      await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "未找到有效的 Session String（可能是二进制文件或格式不支持）");
      return;
    }
    
    await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, `检测到 ${sessionsToTest.length} 个协议号，开始验证并入库...`);
    
    let success = 0;
    let fail = 0;
    const successDetails = [];
    
    const { apiId, apiHash } = getCurrentApiConfig();
    const globalApiId = parseInt(apiId);
    const globalApiHash = String(apiHash);
    
    for (const item of sessionsToTest) {
      try {
        // 兼容新旧格式（字符串 vs 对象）
        let sessionStr = "";
        let finalApiId = globalApiId;
        let finalApiHash = globalApiHash;
        
        if (typeof item === 'string') {
            sessionStr = item;
        } else if (item && item.session) {
            sessionStr = item.session;
            if (item.apiId) finalApiId = item.apiId;
            if (item.apiHash) finalApiHash = item.apiHash;
        }
        
        console.log(`[Import] Testing session: ${sessionStr.substring(0, 10)}... using API ${finalApiId}`);
        const client = new TelegramClient(new StringSession(sessionStr), finalApiId, finalApiHash, { 
          connectionRetries: 1,
          deviceModel: "Desktop", // 伪装成桌面端
          appVersion: "4.16.8 x64",
          systemVersion: "Windows 10",
          useWSS: false,
        });
        await client.connect();
        
        // 尝试获取最新配置以更新 DC
        try { await client.invoke(new Api.help.GetConfig()); } catch {}
        
        // 获取用户信息以确认登录有效
        const me = await client.getMe();
        if (me) {
           console.log(`[Import] Session valid: ${me.id} (${me.phone})`);
           const phone = me.phone || me.id.toString();
           
           const added = addAccount(phone, sessionStr, {
             telegramId: me.id,
             username: me.username || "",
             firstName: me.firstName || "",
             lastName: me.lastName || ""
           });
           
           if (added) {
             success++;
             successDetails.push({
               id: me.id,
               phone: phone,
               name: ((me.firstName || "") + " " + (me.lastName || "")).trim() || "No Name"
             });
           } else {
             fail++; // 重复算失败或忽略
           }
        } else {
           console.log(`[Import] Session invalid (getMe failed)`);
           fail++;
        }
        await client.disconnect();
      } catch (e) {
        console.error("[Import] Session error:", e.message);
        fail++;
      }
    }
    
    let msgText = `✅ 导入完成\n成功：${success}\n失败/重复：${fail}\n总数：${sessionsToTest.length}`;
    if (successDetails.length > 0) {
      msgText += `\n\n📋 **成功导入列表：**\n`;
      // 最多显示 20 条，避免消息过长
      const showList = successDetails.slice(0, 20);
      showList.forEach(d => {
        msgText += `🆔 \`${d.id}\` | 📱 \`${d.phone}\` | 🟢 在线\n`;
      });
      if (successDetails.length > 20) {
        msgText += `...还有 ${successDetails.length - 20} 个账号`;
      }
    }
    
    const kb = new InlineKeyboard().text("添加监控频道", "add_monitor_channel");
    await ctx.api.sendMessage(ctx.chat.id, msgText, { parse_mode: "Markdown", reply_markup: kb });
    
  } catch (e) {
    console.error(e);
    await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "导入失败：" + e.message);
  }
}

bot.callbackQuery("add_monitor_channel", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  userJoinChannelMode.set(ctx.from.id, true);
  await ctx.reply("请发送要加入的频道链接（例如 https://t.me/example 或 @example）：");
  await ctx.answerCallbackQuery();
});

bot.hears(/^\/绑定收录后台$/, async (ctx) => {
  const type = ctx.chat?.type;
  if (type !== "group" && type !== "supergroup" && type !== "channel") {
    await ctx.reply("请在群组或频道中使用该命令");
    return;
  }
  if (type === "channel") {
    try {
      const me = await ctx.api.getMe();
      const member = await ctx.api.getChatMember(ctx.chat.id, me.id);
      const st = member.status;
      if (st !== "administrator" && st !== "creator") {
        await ctx.reply("请先将机器人设置为该频道的管理员再绑定");
        return;
      }
    } catch {
      await ctx.reply("获取权限失败，请确保机器人已在频道内并为管理员");
      return;
    }
  }
  const b = getBinding();
  if (b && b.groupId === ctx.chat.id) {
    await ctx.reply("这个群或频道已经绑定过了");
    return;
  }
  setBinding(ctx.chat.id, ctx.chat.title || "未命名群组");
  await ctx.reply("绑定成功");
  const cat = getSelectedCategory();
  if (cat) {
    await ctx.reply(`当前选择分类是：${cat}\n收录视频的时候注意查看`);
  }
});

bot.hears(/^\/绑定新闻频道$/, async (ctx) => {
  const type = ctx.chat?.type;
  if (type !== "channel") { await ctx.reply("请在新闻频道中使用该命令"); return; }
  try {
    const me = await ctx.api.getMe();
    const member = await ctx.api.getChatMember(ctx.chat.id, me.id);
    const st = member.status;
    if (st !== "administrator" && st !== "creator") { await ctx.reply("请先将机器人设置为该频道的管理员再绑定"); return; }
  } catch { await ctx.reply("获取权限失败，请确保机器人已在频道内并为管理员"); return; }
  const b = getNewsBinding();
  if (b && b.groupId === ctx.chat.id) { await ctx.reply("该新闻频道已经绑定过了"); return; }
  setNewsBinding(ctx.chat.id, ctx.chat.title || "未命名频道");
  await ctx.reply("新闻频道绑定成功");
  const cat = getSelectedCategory();
  if (cat) {
    await ctx.reply(`当前选择分类是：${cat}\n收录视频的时候注意查看`);
  }
});

bot.hears(/^\/关闭$/, async (ctx) => {
  const type = ctx.chat?.type;
  if (type !== "group" && type !== "supergroup") return;
  if (!ctx.from || !isAdmin(ctx.from.id)) {
    await ctx.reply("没有权限执行");
    return;
  }
  setBotEnabled(false);
  await ctx.reply("机器人已停止");
});

bot.hears(/^\/开启$/, async (ctx) => {
  const type = ctx.chat?.type;
  if (type !== "group" && type !== "supergroup") return;
  if (!ctx.from || !isAdmin(ctx.from.id)) {
    await ctx.reply("没有权限执行");
    return;
  }
  setBotEnabled(true);
  await ctx.reply("机器人已开启");
});

bot.catch((err) => {
  try {
    const ctx = err.ctx;
    console.error("Bot error", err.error);
  } catch (e) {
    console.error("Bot error", err);
  }
});

// 交互式登录命令
bot.hears(/^\/添加账号$/, async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) return;
  
  // 初始化状态
  userLoginState.set(ctx.from.id, { step: "phone" });
  await ctx.reply("请发送要登录的账号手机号（格式如 +8613800000000）：");
});

bot.command("test_api", async (ctx) => {
  if (!isAdmin(ctx.from.id)) return;
  const { apiId } = getCurrentApiConfig();
  await ctx.reply(`当前使用的 API ID: ${apiId}\n如果发送验证码失败，请使用 /设置API 修改为你的配置。`);
});

bot.hears(/^\/设置API/, async (ctx) => {
  if (!isAdmin(ctx.from.id)) return;
  const parts = ctx.message.text.split(/\s+/);
  // /设置API 12345 abcde...
  if (parts.length < 3) {
    await ctx.reply("格式错误。\n请前往 https://my.telegram.org/apps 申请，然后发送：\n/设置API <AppID> <AppHash>\n例如：/设置API 123456 abcdef123456");
    return;
  }
  
  const newId = parseInt(parts[1]);
  const newHash = parts[2].trim();
  
  if (!newId || !newHash || newHash.length < 10) {
    await ctx.reply("API ID 或 Hash 格式似乎不正确，请检查。");
    return;
  }
  
  setApiConfig(newId, newHash);
  await ctx.reply(`✅ API 配置已更新！\nID: ${newId}\nHash: ${newHash}\n请重试 /添加账号`);
});

// 监听所有文本消息，处理登录流程
bot.on("message", async (ctx, next) => {
  const uid = ctx.from?.id;
  if (!uid) return next();
  const text = ctx.message.text ? ctx.message.text.trim() : "";
  if (!text) return next();
  
  // console.log(`[Bot] Received message from ${uid}: ${text}`); // 移除调试日志，减少刷屏

  // 监听直接发送的 QR Token (用户发送从网页复制的 Token)
  // 如果是 32 位 hex，可能是 token
  if (text.length === 32 && /^[0-9a-f]+$/.test(text)) {
     const row = getQrToken(text);
     if (row) {
       userSteps.set(uid, { step: "qr_wait_session", token: text });
       await ctx.reply("✅ 识别到登录请求。请直接发送您的 Session String（或包含 Session 的文件），我将为您同步到网页后台。");
       return; // 结束处理
     }
  }

  // 拦截非管理员的所有私聊消息（除了 /start，因为 /start 已经单独处理了）
  // 注意：这里需要放行处于 userSteps 或 userLoginState 状态的用户
  if (ctx.from && !isAdmin(ctx.from.id)) {
     const isStart = text.startsWith("/start");
     const hasStep = userSteps.has(ctx.from.id);
     const hasLogin = userLoginState.has(ctx.from.id);
     const hasJR = userJoinRequestState.has(ctx.from.id);
     const hasChristmas = christmasState.has(ctx.from.id);
     const addingSupport = userAddSupportMode.has(ctx.from.id);
     
     if (!isStart && !hasStep && !hasLogin && !hasJR && !hasChristmas && !addingSupport && !isSupport(ctx.from.id)) {
        // console.log(`[Msg] Intercepted non-admin: ${ctx.from.id}`);
        await ctx.reply("你不是管理员 没办法使用");
        return;
     }
  }
  
  // 如果处于等待 session 状态
  const step = userSteps.get(uid);
  if (step && step.step === "qr_wait_session") {
     if (text.length > 20 && /^[a-zA-Z0-9+/=_ -]+$/.test(text)) {
        // 尝试作为 session string 处理
        try {
          await ctx.reply("正在验证 Session...");
          const { apiId, apiHash } = getCurrentApiConfig();
          const client = new TelegramClient(new StringSession(text), parseInt(apiId), String(apiHash), { connectionRetries: 1 });
          await client.connect();
          const me = await client.getMe();
          if (me) {
             // 更新 token 对应的 session，让网页端轮询到
             updateQrToken(step.token, text); // 这里的 text 是 session string
             await ctx.reply(`✅ 验证成功！账号 ${me.phone} 已同步到网页后台。`);
             userSteps.delete(uid);
          } else {
             await ctx.reply("❌ Session 无效，请重新发送。");
          }
          await client.disconnect();
        } catch(e) {
          await ctx.reply("❌ 验证失败: " + e.message);
        }
        return;
     }
  }

  // 添加客服流程
  if (userAddSupportMode.get(uid)) {
    if (!isAdmin(uid)) { userAddSupportMode.delete(uid); return next(); }
    const raw = text;
    let targetId = 0;
    if (/^\d+$/.test(raw)) {
      targetId = parseInt(raw);
    } else if (raw.startsWith("@")) {
      const user = getUserByUsername(raw);
      if (user) {
        targetId = user.id;
      } else {
        await ctx.reply("未找到该用户名，请确保该用户使用过本机器人，或直接发送数字ID。");
        return;
      }
    } else {
      await ctx.reply("格式错误。请发送 @username 或数字ID。");
      return;
    }
    if (targetId) {
      addSupport(targetId);
      userAddSupportMode.delete(uid);
      await ctx.reply(`✅ 已成功将 ${targetId} 添加为客服！`);
    } else {
      await ctx.reply("无法获取目标信息");
    }
    return;
  }

  // 进群申请流程：等待用户输入公群编号
  const jr = userJoinRequestState.get(uid);
  if (jr && jr.step === "await_code") {
    setJoinRequestCode(jr.chatId, uid, text);
    userJoinRequestState.set(uid, { ...jr, step: "await_guarantor" });
    const kb = new InlineKeyboard().text("新币", "guarantor:xinbi").text("土豆", "guarantor:tudou");
    await ctx.reply("请选择对应的担保", { reply_markup: kb });
    return;
  }
  
  const chs = christmasState.get(uid);
  if (chs) {
    if (hasChristmasWish(chs.chatId, uid)) {
      await ctx.reply("你已经许愿了 如需修改 请联系管理员");
      christmasState.delete(uid);
      return;
    }
    addChristmasWish(chs.chatId, uid, text);
    await ctx.reply("你的愿望已经被存储在数据库");
    christmasState.delete(uid);
    return;
  }
  
  const state = userLoginState.get(uid);
  if (!state) return next(); // 没有处于登录流程
  
  // 取消操作
  if (text === "/cancel" || text === "取消") {
    if (state.client) {
      await state.client.disconnect();
    }
    userLoginState.delete(uid);
    await ctx.reply("已取消登录操作。");
    return;
  }
  
  try {
    // 步骤1：输入手机号
    if (state.step === "phone") {
      if (!text.startsWith("+") && !/^\d+$/.test(text)) {
        await ctx.reply("手机号格式错误，请以 + 开头，例如 +86...");
        return;
      }
      
      const statusMsg = await ctx.reply("正在连接服务器并发送验证码...");
      
      const { apiId, apiHash } = getCurrentApiConfig();
      
      if (!apiId || typeof apiId !== 'number' || !apiHash || typeof apiHash !== 'string') {
        await ctx.reply(`API 配置错误：ID=${apiId} (${typeof apiId}), Hash=${apiHash} (${typeof apiHash})。请使用 /设置API 重新配置。`);
        return;
      }

      const client = new TelegramClient(new StringSession(""), apiId, apiHash, { 
        connectionRetries: 5,
        deviceModel: "CopyExtractBot",
        appVersion: "1.0.0",
        systemVersion: "Windows 10"
      });
      await client.connect();
      
      try {
        console.log(`[Login] Sending code to ${text}`);
        // 仅传递 phone，依赖 client 初始化时的 apiId/Hash
        const { phoneCodeHash, isCodeViaApp } = await client.sendCode({
          phone: text,
        });
        
        // 更新状态
        state.client = client;
        state.phone = text;
        state.phoneCodeHash = phoneCodeHash;
        state.step = "code";
        userLoginState.set(uid, state);
        
        await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, 
          `✅ 验证码已发送！\n请查看 Telegram 官方通知（或短信）。\n\n请直接回复验证码（如果是纯数字，建议格式如 12345）：`
        );
      } catch (e) {
        console.error("Send code error:", e);
        await client.disconnect();
        userLoginState.delete(uid);
        
        if (e.message.includes("PHONE_NUMBER_INVALID")) {
          await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "❌ 手机号无效");
        } else if (e.message.includes("FLOOD")) {
          await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "❌ 请求太频繁 (FloodWait)，请稍后再试");
        } else {
          await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "❌ 发送验证码失败: " + e.message);
        }
      }
      return;
    }
    
    // 步骤2：输入验证码
    if (state.step === "code") {
      // 有些用户可能会输入 "c12345" 或 "code 12345"
      let code = text.replace(/[^0-9]/g, "");
      if (!code) {
        await ctx.reply("请输入有效的数字验证码");
        return;
      }
      
      const statusMsg = await ctx.reply("正在验证...");
      
      try {
        await state.client.invoke(new Api.auth.SignIn({
          phoneNumber: state.phone,
          phoneCodeHash: state.phoneCodeHash,
          phoneCode: code,
        }));
        
        // 登录成功
        const session = state.client.session.save();
        const me = await state.client.getMe();
        
        addAccount(me.phone || state.phone, session);
        
        await state.client.disconnect();
        userLoginState.delete(uid);
        
        const kb = new InlineKeyboard().text("添加监控频道", "add_monitor_channel");
        await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, `✅ 登录成功！\n账号：${me.firstName} (${me.phone})\n已保存到数据库。`, { reply_markup: kb });
        
      } catch (e) {
        if (e.message.includes("SESSION_PASSWORD_NEEDED")) {
          // 需要 2FA 密码
          state.step = "password";
          userLoginState.set(uid, state);
          await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "🔐 该账号开启了两步验证，请输入密码：");
        } else if (e.message.includes("PHONE_CODE_INVALID")) {
          await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "❌ 验证码错误，请重新输入，或发送 /cancel 取消");
        } else {
          console.error("Sign in error:", e);
          await state.client.disconnect();
          userLoginState.delete(uid);
          await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "❌ 登录失败: " + e.message);
        }
      }
      return;
    }
    
    // 步骤3：输入 2FA 密码
    if (state.step === "password") {
      const password = text;
      const statusMsg = await ctx.reply("正在验证密码...");
      
      try {
        await state.client.signIn({ password: password, phoneNumber: state.phone, phoneCodeHash: state.phoneCodeHash });
        
        const session = state.client.session.save();
        const me = await state.client.getMe();
        
        addAccount(me.phone || state.phone, session);
        
        await state.client.disconnect();
        userLoginState.delete(uid);
        
        const kb = new InlineKeyboard().text("添加监控频道", "add_monitor_channel");
        await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, `✅ 登录成功！\n账号：${me.firstName} (${me.phone})\n已保存到数据库。`, { reply_markup: kb });
        
      } catch (e) {
        if (e.message.includes("PASSWORD_HASH_INVALID")) {
           await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "❌ 密码错误，请重新输入，或发送 /cancel 取消");
        } else {
           console.error("2FA error:", e);
           await state.client.disconnect();
           userLoginState.delete(uid);
           await ctx.api.editMessageText(ctx.chat.id, statusMsg.message_id, "❌ 登录失败: " + e.message);
        }
      }
      return;
    }
    
  } catch (e) {
    console.error("Login flow error:", e);
    userLoginState.delete(uid);
  }
  
  return next();
});

bot.on("message", async (ctx, next) => {
  const msg = ctx.update.message;
  console.log(`[Msg] From: ${ctx.from?.id}, Text: ${msg.text}, Type: ${ctx.chat?.type}, MediaGroup: ${msg.media_group_id}`);
  
  if (ctx.chat?.type === "private") {
    if (ctx.from) {
      upsertUser(ctx.from.id, ctx.from.first_name, ctx.from.last_name, ctx.from.username);
    }
    
    // 超级管理员添加管理员逻辑
    if (ctx.from && ctx.from.id === SUPER_ADMIN_ID && userAddAdminMode.get(ctx.from.id)) {
       // ... (省略)
       const text = msg.text?.trim();
       if (!text || !/^\d+$/.test(text)) {
         await ctx.reply("格式错误，请发送纯数字 ID，或点击取消");
         return;
       }
       const newAdminId = parseInt(text);
       addAdmin(newAdminId);
       userAddAdminMode.delete(ctx.from.id);
       
       const kb = new InlineKeyboard().text("返回管理员管理", "manage_admins");
       await ctx.reply(`✅ 已成功添加管理员：${newAdminId}`, { reply_markup: kb });
       return;
    }

    // 协议号监控频道逻辑
    if (userJoinChannelMode.get(ctx.from.id)) {
      console.log(`[JoinChannel] User ${ctx.from.id} sent link: ${msg.text}`);
      if (!msg.text) { await ctx.reply("请发送频道链接"); return; }
      const link = msg.text.trim();
      
      // 检查是否是私有频道邀请链接 (t.me/+AbCdEf...)
      // 兼容更多格式：https://t.me/+... 或 t.me/+...
      const inviteMatch = link.match(/(?:t\.me\/|telegram\.me\/)\+([a-zA-Z0-9_\-]+)/);
      let username = "";
      let inviteHash = "";
      
      if (inviteMatch) {
        inviteHash = inviteMatch[1];
        console.log(`[JoinChannel] Detected Invite Hash: ${inviteHash}`);
      } else {
        if (link.includes("t.me/") || link.includes("telegram.me/")) {
          // 处理 t.me/joinchat/AbCdEf... 格式
          if (link.includes("/joinchat/")) {
             inviteHash = link.split("/joinchat/")[1].split("/")[0].split("?")[0];
             console.log(`[JoinChannel] Detected JoinChat Hash: ${inviteHash}`);
          } else {
             // 标准链接 t.me/username
             // 移除 https:// 或 http://
             const clean = link.replace(/^https?:\/\//, "");
             const parts = clean.split("/");
             // parts: [t.me, username, ...]
             if (parts.length >= 2) {
                username = parts[1].split("?")[0];
             }
             console.log(`[JoinChannel] Detected Username from URL: ${username}`);
          }
        } else if (link.startsWith("@")) {
          username = link.substring(1);
          console.log(`[JoinChannel] Detected Username from @: ${username}`);
        } else {
          // 纯用户名
          username = link;
          console.log(`[JoinChannel] Assumed Username: ${username}`);
        }
      }
      
      // 如果既没有 username 也没有 inviteHash，报错
      if (!username && !inviteHash) {
         await ctx.reply("无法识别频道链接，请发送标准链接 (t.me/xxx) 或邀请链接 (t.me/+xxx)");
         return;
      }
      
      userJoinChannelMode.delete(ctx.from.id);
      await ctx.reply(`正在尝试让所有协议号加入频道 ${inviteHash ? '(私有邀请)' : '@'+username}，请稍候...`);
      
      // 只获取状态为 ok 的账号
      const allAccounts = listAccounts();
      const accounts = allAccounts.filter(a => a.status === 'ok' && a.phone);
      
      if (!accounts.length) {
        await ctx.reply("暂无可用协议号 (Status: OK)，请先导入或检查账号状态");
        return;
      }
      
      const { apiId, apiHash } = getCurrentApiConfig();
      const globalApiId = parseInt(apiId);
      const globalApiHash = String(apiHash);

      let success = 0;
      let fail = 0;
      const failReasons = [];
      
      for (const acc of accounts) {
        try {
          // 尝试解析 session string 获取专属 apiId/hash (如果之前存了的话)
          // 现在的 db 结构只存了 session string，所以这里只能用全局或默认
          
          const client = new TelegramClient(new StringSession(acc.session_string), globalApiId, globalApiHash, { 
              connectionRetries: 1,
              deviceModel: "Desktop", 
              appVersion: "4.16.8 x64",
              useWSS: false
          });
          await client.connect();
          
          if (inviteHash) {
             await client.invoke(new Api.messages.ImportChatInvite({ hash: inviteHash }));
          } else {
             // 必须先解析 username 获取实体对象，直接传字符串会报错
             const entity = await client.getEntity(username);
             await client.invoke(new Api.channels.JoinChannel({ channel: entity }));
          }
          
          await client.disconnect();
          success++;
        } catch (e) {
          console.error(`Account ${acc.phone} failed to join:`, e.message);
          
          if (e.message.includes("USER_ALREADY_PARTICIPANT")) {
             success++; // 已经在频道里了算成功
          } else {
             fail++;
             const reason = e.message.split(":")[0] || e.message;
             if (!failReasons.includes(reason)) failReasons.push(reason);
             
             // 如果是 session 失效，可以考虑标记为 invalid
             if (e.message.includes("AUTH_KEY_UNREGISTERED") || e.message.includes("SESSION_REVOKED")) {
               deleteAccount(acc.session_string);
             }
          }
        }
      }
      
      let replyText = `✅ 操作完成\n成功加入：${success} 个\n失败：${fail} 个`;
      if (fail > 0 && failReasons.length > 0) {
        replyText += `\n\n❌ 失败原因：\n${failReasons.join("\n")}`;
      }
      
      await ctx.reply(replyText);
      return;
    }
    
    if (adminDmVerifyMode.get(ctx.from.id)) {
      const text = (msg.text || "").trim();
      let targetId = 0;
      if (/^\d+$/.test(text)) {
        targetId = parseInt(text);
      } else if (/^@?[A-Za-z0-9_]{5,}$/.test(text)) {
        const row = getUserByUsername(text);
        if (row && row.id) targetId = row.id;
      }
      if (!targetId) {
        await ctx.reply("未找到用户ID，请发送纯数字ID或用户名（@username）");
        return;
      }
      try {
        await bot.api.sendMessage(targetId, "你好");
        await ctx.reply(`已私聊用户 ${targetId}`);
      } catch (e) {
        try {
          if (!BOT_USERNAME) {
            const me = await bot.api.getMe();
            BOT_USERNAME = me.username || "";
          }
          if (BOT_USERNAME) {
            const url = `https://t.me/${BOT_USERNAME}?start=hello_${targetId}`;
            await ctx.reply(`无法主动私聊，请让用户点击：\n${url}`);
          } else {
            await ctx.reply("无法主动私聊，且机器人用户名不可用");
          }
        } catch {
          await ctx.reply("无法主动私聊");
        }
      } finally {
        adminDmVerifyMode.delete(ctx.from.id);
      }
      return;
    }
    
    // 拦截非管理员的所有私聊消息（除了 /start，因为 /start 已经单独处理了）
    // 已经在前面处理了，这里移除旧的逻辑
    /*
    if (ctx.from && !isAdmin(ctx.from.id) && msg.text !== "/start") {
      console.log(`[Msg] Intercepted non-admin: ${ctx.from.id}`);
      await ctx.reply("你不是管理员 没办法使用");
      return;
    }
    */

    if (msg.media_group_id && msg.caption) {
      console.log(`[Msg] Caching caption for group ${msg.media_group_id}: ${msg.caption.substring(0, 20)}...`);
      groupCaptionCache.set(msg.media_group_id, msg.caption);
      setTimeout(() => groupCaptionCache.delete(msg.media_group_id), 60000);
    }
  }
  await next();
});

bot.on("message:video", async (ctx) => {
  const msg = ctx.update.message;
  console.log(`[Video] Received video from ${ctx.from?.id}`);
  const type = ctx.chat?.type;
  if (type !== "private") return;
  if (!getBotEnabled()) {
    await ctx.reply("机器人已停止");
    return;
  }
  if (ctx.from) {
    upsertUser(ctx.from.id, ctx.from.first_name, ctx.from.last_name, ctx.from.username);
  }
  const video = msg.video;
  const mode = ctx.from ? (userModes.get(ctx.from.id) || "normal") : "normal";
  const extract = getGlobalExtractMode();
  if (msg.media_group_id) {
    console.log(`[Video] Adding to MediaGroup ${msg.media_group_id}`);
    addMediaGroupPart(ctx, "video", video.file_id, msg.media_group_id, msg.caption || "");
    return;
  }
  const b = mode === "news" ? getNewsBinding() : getBinding();
  if (!b || !b.groupId) {
    await ctx.reply(mode==='news' ? "未绑定新闻频道，请先在新闻频道发送 /绑定新闻频道" : "未绑定后台群，请先在群中发送 /绑定收录后台");
    return;
  }
  const uniqueId = video.file_unique_id;
  if (hasUnique(uniqueId) || hasPostByFileId(video.file_id)) {
    await ctx.reply("这个视频已在数据库");
    return;
  }
  let caption = msg.caption || (msg.media_group_id ? (groupCaptionCache.get(msg.media_group_id) || "") : "");
  if (!caption && msg.media_group_id) {
    await new Promise((r) => setTimeout(r, 1500));
    caption = groupCaptionCache.get(msg.media_group_id) || "";
  }
  const suffix = "\n➖➖➖➖➖➖➖➖\n❤️关注防失联❤️ @hxkpbot\n➖➖➖➖➖➖➖➖";
  const cleaned = sanitizeCaption(caption||"");
  let finalCaption = "";
  if (extract === "v") {
    finalCaption = "";
  } else {
    // 无论是新闻模式还是普通模式，只要不是“仅视频”，都加上这个后缀
    // 如果原逻辑是 news 模式才加后缀，现在改为统一添加
    finalCaption = safeCaption(cleaned + suffix);
  }
  try {
    await enqueueSendVideo(b.groupId, video.file_id, finalCaption, ctx.from?.id || 0);
    insertPost(ctx.from.id, video.file_id, caption);
    addUnique(uniqueId);
    await ctx.reply(mode==='news' ? "已按新闻模式转发" : (extract==="v" ? "已提取视频并转发到后台" : "已提取视频与文案并转发到后台"));
  } catch (e) {
    await ctx.reply("转发失败，请检查绑定目标权限或是否为频道管理员");
  }
});

bot.on("message:photo", async (ctx) => {
  const msg = ctx.update.message;
  console.log(`[Photo] Received photo from ${ctx.from?.id}`);
  const type = ctx.chat?.type;
  if (type !== "private") return;
  if (ctx.from && userUploadMode.get(ctx.from.id)) {
    const caption = msg.caption || "";
    const names = extractHandles(caption);
    if (names.length) {
      const res = await saveNamesWithDup(ctx.from.id, names);
      await ctx.reply(res.message);
      userUploadMode.delete(ctx.from.id);
    } else {
      await ctx.reply("未检测到用户名，请发送文本，每行一个");
    }
    return;
  }
  if (!getBotEnabled()) { await ctx.reply("机器人已停止"); return; }
  const mode = ctx.from ? (userModes.get(ctx.from.id) || "normal") : "normal";
  const extract = getGlobalExtractMode();
  if (msg.media_group_id) {
    const photos = msg.photo || [];
    const file = photos[photos.length-1];
    console.log(`[Photo] Adding to MediaGroup ${msg.media_group_id}`);
    addMediaGroupPart(ctx, "photo", file.file_id, msg.media_group_id, msg.caption || "");
    return;
  }
  if (mode === "news") {
    const b = getNewsBinding();
    if (!b || !b.groupId) { await ctx.reply("未绑定新闻频道，请先在新闻频道发送 /绑定新闻频道"); return; }
    const photos = msg.photo || [];
    const file = photos[photos.length-1];
    let caption = msg.caption || (msg.media_group_id ? (groupCaptionCache.get(msg.media_group_id) || "") : "");
    if (!caption && msg.media_group_id) { await new Promise((r)=>setTimeout(r,1500)); caption = groupCaptionCache.get(msg.media_group_id) || ""; }
    const suffix = "\n➖➖➖➖➖➖➖➖\n❤️关注防失联❤️ @hxkpbot\n➖➖➖➖➖➖➖➖";
    const finalCaption = safeCaption(sanitizeCaption(caption||"") + suffix);
    try {
      await ctx.api.sendPhoto(b.groupId, file.file_id, { caption: finalCaption });
      await ctx.reply("已按新闻模式转发图片");
    } catch (e) {
      await ctx.reply("转发失败，请检查绑定目标权限或是否为频道管理员");
    }
    return;
  }
  if (extract === "vci" || extract === "all") {
    const b = getBinding();
    if (!b || !b.groupId) { await ctx.reply("未绑定后台群，请先在群中发送 /绑定收录后台"); return; }
    const photos = msg.photo || [];
    const file = photos[photos.length-1];
    const caption = msg.caption || "";
    const finalCaption = safeCaption(sanitizeCaption(caption || ""));
    try {
      await ctx.api.sendPhoto(b.groupId, file.file_id, { caption: finalCaption });
      await ctx.reply("已提取图片并转发到后台");
    } catch (e) {
      await ctx.reply("转发失败，请检查绑定目标权限或是否为频道管理员");
    }
    return;
  }
  await ctx.reply("当前模式下不处理图片");
});

function addMediaGroupPart(ctx, kind, fileId, groupId, captionText) {
  const uid = ctx.from?.id || 0;
  let g = mediaGroups.get(groupId);
  if (!g) {
    const mode = getGlobalExtractMode(); // 直接获取全局模式
    console.log(`[MediaGroup] New group ${groupId}, uid: ${uid}, mode: ${mode}`);
    g = { items: [], uid, chatId: ctx.chat?.id || 0, mode: userModes.get(uid) || "normal", extract: mode, caption: "", timer: null };
    mediaGroups.set(groupId, g);
  }
  // 关键修正：始终尝试更新 caption，不仅仅是 !g.caption 时
  // 因为 Telegram 可能会把 caption 放在 MediaGroup 的中间或最后一条消息里
  // 之前的逻辑是：只要 g.caption 有值了就不再更新，但有可能第一条消息没 caption，第二条才有
  // 或者 groupCaptionCache 里的值可能滞后
  const c = captionText || (groupCaptionCache.get(groupId) || "");
  if (c && !g.caption) {
    g.caption = c;
    console.log(`[MediaGroup] Found caption for ${groupId}: ${c.substring(0, 20)}...`);
  } else if (c && g.caption && c.length > g.caption.length) {
     // 如果新的 caption 比旧的长（例如旧的是空字符串或部分），更新它
     g.caption = c;
     console.log(`[MediaGroup] Updated caption for ${groupId}: ${c.substring(0, 20)}...`);
  }
  
  g.items.push({ kind, fileId });
  if (g.timer) clearTimeout(g.timer);
  g.timer = setTimeout(() => processMediaGroup(groupId), 1500);
}

async function processMediaGroup(groupId) {
  console.log(`[ProcessGroup] Processing ${groupId}`);
  const g = mediaGroups.get(groupId);
  if (!g) {
    console.log(`[ProcessGroup] Group ${groupId} not found (maybe already processed)`);
    return;
  }
  mediaGroups.delete(groupId);
  const mode = g.mode || "normal";
  
  const globalMode = getGlobalExtractMode();
  const extract = globalMode || "vc"; // 优先使用全局设置
  console.log(`[ProcessGroup] Mode: ${mode}, Extract: ${extract}, Items: ${g.items.length}`);

  const target = mode === "news" ? getNewsBinding() : getBinding();
  if (!target || !target.groupId) {
    console.log(`[ProcessGroup] No target binding found`);
    await bot.api.sendMessage(g.chatId, mode==='news' ? "未绑定新闻频道" : "未绑定后台群");
    return;
  }
  // ...
}

bot.on("message:video", async (ctx) => {
  const type = ctx.chat?.type;
  if (type !== "private") return;
  if (!getBotEnabled()) {
    await ctx.reply("机器人已停止");
    return;
  }
  if (ctx.from) {
    upsertUser(ctx.from.id, ctx.from.first_name, ctx.from.last_name, ctx.from.username);
  }
  const msg = ctx.update.message;
  const video = msg.video;
  const mode = ctx.from ? (userModes.get(ctx.from.id) || "normal") : "normal";
  const extract = getGlobalExtractMode();
  if (msg.media_group_id) {
    addMediaGroupPart(ctx, "video", video.file_id, msg.media_group_id, msg.caption || "");
    return;
  }
  const b = mode === "news" ? getNewsBinding() : getBinding();
  if (!b || !b.groupId) {
    await ctx.reply(mode==='news' ? "未绑定新闻频道，请先在新闻频道发送 /绑定新闻频道" : "未绑定后台群，请先在群中发送 /绑定收录后台");
    return;
  }
  const uniqueId = video.file_unique_id;
  if (hasUnique(uniqueId) || hasPostByFileId(video.file_id)) {
    await ctx.reply("这个视频已在数据库");
    return;
  }
  let caption = msg.caption || (msg.media_group_id ? (groupCaptionCache.get(msg.media_group_id) || "") : "");
  if (!caption && msg.media_group_id) {
    await new Promise((r) => setTimeout(r, 1500));
    caption = groupCaptionCache.get(msg.media_group_id) || "";
  }
  const suffix = "\n➖➖➖➖➖➖➖➖\n❤️关注防失联❤️ @hxkpbot\n➖➖➖➖➖➖➖➖";
  const cleaned = sanitizeCaption(caption||"");
  let finalCaption = "";
  if (extract === "v") {
    finalCaption = "";
  } else {
    finalCaption = safeCaption(mode==='news' ? (cleaned + suffix) : cleaned);
  }
  try {
    await enqueueSendVideo(b.groupId, video.file_id, finalCaption, ctx.from?.id || 0);
    insertPost(ctx.from.id, video.file_id, caption);
    addUnique(uniqueId);
    await ctx.reply(mode==='news' ? "已按新闻模式转发" : (extract==="v" ? "已提取视频并转发到后台" : "已提取视频与文案并转发到后台"));
  } catch (e) {
    await ctx.reply("转发失败，请检查绑定目标权限或是否为频道管理员");
  }
});

bot.on("message:photo", async (ctx) => {
  const type = ctx.chat?.type;
  if (type !== "private") return;
  if (ctx.from && userUploadMode.get(ctx.from.id)) {
    const msg = ctx.update.message;
    const caption = msg.caption || "";
    const names = extractHandles(caption);
    if (names.length) {
      const res = await saveNamesWithDup(ctx.from.id, names);
      await ctx.reply(res.message);
      userUploadMode.delete(ctx.from.id);
    } else {
      await ctx.reply("未检测到用户名，请发送文本，每行一个");
    }
    return;
  }
  if (!getBotEnabled()) { await ctx.reply("机器人已停止"); return; }
  const mode = ctx.from ? (userModes.get(ctx.from.id) || "normal") : "normal";
  const extract = getGlobalExtractMode();
  if (msg.media_group_id) {
    const photos = msg.photo || [];
    const file = photos[photos.length-1];
    addMediaGroupPart(ctx, "photo", file.file_id, msg.media_group_id, msg.caption || "");
    return;
  }
  const msg = ctx.update.message;
  if (mode === "news") {
    const b = getNewsBinding();
    if (!b || !b.groupId) { await ctx.reply("未绑定新闻频道，请先在新闻频道发送 /绑定新闻频道"); return; }
    const photos = msg.photo || [];
    const file = photos[photos.length-1];
    let caption = msg.caption || (msg.media_group_id ? (groupCaptionCache.get(msg.media_group_id) || "") : "");
    if (!caption && msg.media_group_id) { await new Promise((r)=>setTimeout(r,1500)); caption = groupCaptionCache.get(msg.media_group_id) || ""; }
    const suffix = "\n➖➖➖➖➖➖➖➖\n❤️关注防失联❤️ @hxkpbot\n➖➖➖➖➖➖➖➖";
    const finalCaption = safeCaption(sanitizeCaption(caption||"") + suffix);
    try {
      await ctx.api.sendPhoto(b.groupId, file.file_id, { caption: finalCaption });
      await ctx.reply("已按新闻模式转发图片");
    } catch (e) {
      await ctx.reply("转发失败，请检查绑定目标权限或是否为频道管理员");
    }
    return;
  }
  if (extract === "vci" || extract === "all") {
    const b = getBinding();
    if (!b || !b.groupId) { await ctx.reply("未绑定后台群，请先在群中发送 /绑定收录后台"); return; }
    const photos = msg.photo || [];
    const file = photos[photos.length-1];
    const caption = msg.caption || "";
    const finalCaption = safeCaption(sanitizeCaption(caption || ""));
    try {
      await ctx.api.sendPhoto(b.groupId, file.file_id, { caption: finalCaption });
      await ctx.reply("已提取图片并转发到后台");
    } catch (e) {
      await ctx.reply("转发失败，请检查绑定目标权限或是否为频道管理员");
    }
    return;
  }
  await ctx.reply("当前模式下不处理图片");
});

bot.command("绑定收录后台", async (ctx) => {
  const type = ctx.chat.type;
  if (type === "private") {
    await ctx.reply("请在群组或频道中使用此命令");
    return;
  }
  
  // 检查是否为管理员
  const uid = ctx.from?.id;
  if (!uid || !isAdmin(uid)) {
    // 即使在群里，如果触发命令的人不是机器人管理员，也不允许绑定（防止被恶意绑定）
    // 但在频道中，消息可能没有 from 字段（匿名发送），这种情况下通常认为是管理员操作
    // 为了安全，我们还是尽量检查 isAdmin。如果 ctx.from 存在且不是 admin，拒绝。
    if (uid && !isAdmin(uid)) {
      // 这里的 isAdmin 检查的是“机器人管理员”，即数据库里的 admins
      // 只有被授权的机器人管理员才能把群/频道绑定为后台
      return; 
    }
  }

  // 获取群组/频道信息
  const chat = ctx.chat;
  const title = chat.title || "未命名";
  
  setBinding(chat.id, title);
  await ctx.reply(`✅ 绑定成功！\n当前群组/频道 [${title}] 已设为默认转发收录后台。`);
});

bot.command("绑定新闻频道", async (ctx) => {
  const type = ctx.chat.type;
  if (type === "private") {
    await ctx.reply("请在群组或频道中使用此命令");
    return;
  }
  
  const uid = ctx.from?.id;
  if (uid && !isAdmin(uid)) return;

  const chat = ctx.chat;
  const title = chat.title || "未命名";
  
  setNewsBinding(chat.id, title);
  await ctx.reply(`✅ 绑定成功！\n当前群组/频道 [${title}] 已设为新闻模式转发目标。`);
});

bot.command("admin", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.reply("没有权限执行"); return; }
  const limit = 5;
  const total = countUsers();
  const rows = listUsers(limit, 0);
  const lines = rows.map((u) => {
    const name = ((u.first_name || "") + " " + (u.last_name || "")).trim() || (u.username ? "@" + u.username : "未设置昵称");
    const uname = u.username ? "@" + u.username : "";
    return `${name} id:${u.id} ${uname}`.trim();
  });
  const text = `所有用户数量 ${total}\n` + (lines.join("\n") || "暂无用户");
  const kb = new InlineKeyboard().text("私聊验证", "admin_dm_verify");
  if (total > limit) kb.text("下一页", "users_page:2");
  await ctx.reply(text, { reply_markup: kb });
});

bot.callbackQuery(/users_page:(\d+)/, async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  const limit = 5;
  const total = countUsers();
  const page = parseInt(ctx.match[1]);
  const offset = (page - 1) * limit;
  const rows = listUsers(limit, offset);
  const lines = rows.map((u) => {
    const name = ((u.first_name || "") + " " + (u.last_name || "")).trim() || (u.username ? "@" + u.username : "未设置昵称");
    const uname = u.username ? "@" + u.username : "";
    return `${name} id:${u.id} ${uname}`.trim();
  });
  const text = `所有用户数量 ${total}\n` + (lines.join("\n") || "暂无用户");
  const kb = new InlineKeyboard();
  if (page > 1) kb.text("上一页", `users_page:${page - 1}`);
  if (page * limit < total) kb.text("下一页", `users_page:${page + 1}`);
  await ctx.editMessageText(text, { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.command("clean", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) {
    await ctx.reply("没有权限执行");
    return;
  }
  const id = ctx.from.id;
  const step = cleanSteps.get(id) || 0;
  if (step === 0) {
    cleanSteps.set(id, 1);
    await ctx.reply("危险操作：清理全部收录与缓存。再次发送 /clean 进行第2步确认");
    return;
  }
  if (step === 1) {
    cleanSteps.set(id, 2);
    await ctx.reply("最后一步：请输入管理员的密码证明，使用命令 /clean_pwd <密码> 进行最终确认");
    return;
  }
  await ctx.reply("请使用 /clean_pwd <密码> 完成最终确认");
});

bot.command("clean_pwd", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) {
    await ctx.reply("没有权限执行");
    return;
  }
  const text = ctx.match ? ctx.match[0] : ctx.message.text;
  const parts = text.split(/\s+/);
  const pwd = parts[1] || "";
  if (pwd !== "201043") {
    await ctx.reply("密码错误，已取消");
    cleanSteps.delete(ctx.from.id);
    return;
  }
  const cnt = backupPosts();
  const deleted = clearPosts();
  groupCaptionCache.clear();
  cleanSteps.delete(ctx.from.id);
  await ctx.reply(`已清理缓存与历史数据，删除 ${deleted} 条；已创建备份 ${cnt} 条，可用 /恢复备份 还原`);
});

bot.command("恢复备份", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) {
    await ctx.reply("没有权限执行");
    return;
  }
  if (!hasBackup()) {
    await ctx.reply("没有可用备份");
    return;
  }
  const restored = restorePostsFromBackup();
  await ctx.reply(`已恢复 ${restored} 条历史收录`);
});

const userWebLoginState = new Map(); // web端登录状态: { token: string, client: TelegramClient, phone: string, phoneCodeHash: string }
const userJoinRequestState = new Map(); // 进群申请状态: { chatId: number, deadline: number, step: 'await_verify' }
const userCaptchaState = new Map(); // 人机验证状态: { chatId, nonce, answer, expires, attempts }
const christmasState = new Map();
let BOT_USERNAME = "";
const adminDmVerifyMode = new Map();

bot.command("邀请", async (ctx) => {
  const kb = new InlineKeyboard().text("生成邀请链接", "gen_invite_link").row().text("下级管理", "manage_referrals");
  await ctx.reply("邀请功能", { reply_markup: kb });
});

bot.callbackQuery("gen_invite_link", async (ctx) => {
  await ctx.answerCallbackQuery();
  const b = getBinding();
  if (!b || !b.groupId) {
    await ctx.reply("请先在目标群组使用 /绑定收录后台");
    return;
  }
  const uid = ctx.from?.id || 0;
  try {
    const name = `inv_${uid}_${Date.now()}`;
    const link = await bot.api.createChatInviteLink(b.groupId, { name, creates_join_request: true });
    addInviteLink(b.groupId, uid, link.invite_link, name);
    await ctx.reply(`你的群组专属邀请链接：\n${link.invite_link}`);
  } catch (e) {
    await ctx.reply("无法生成邀请链接，请确保机器人在该群具有管理员权限");
  }
});

bot.callbackQuery("manage_referrals", async (ctx) => {
  await ctx.answerCallbackQuery();
  const uid = ctx.from?.id || 0;
  const limit = 10;
  const total = countReferrals(uid);
  const rows = listReferrals(uid, limit, 0);
  const lines = rows.map(r => `用户 ${r.invitee_id} 加入聊天 ${r.chat_id}`);
  const text = `已邀请人数 ${total}\n` + (lines.join("\n") || "暂无数据");
  const kb = new InlineKeyboard();
  if (total > limit) kb.text("下一页", "referrals_page:2");
  await ctx.reply(text, { reply_markup: kb });
});

bot.callbackQuery(/referrals_page:(\d+)/, async (ctx) => {
  await ctx.answerCallbackQuery();
  const uid = ctx.from?.id || 0;
  const limit = 10;
  const page = parseInt(ctx.match[1]);
  const total = countReferrals(uid);
  const offset = (page - 1) * limit;
  const rows = listReferrals(uid, limit, offset);
  const lines = rows.map(r => `用户 ${r.invitee_id} 加入聊天 ${r.chat_id}`);
  const text = `已邀请人数 ${total}\n` + (lines.join("\n") || "暂无数据");
  const kb = new InlineKeyboard();
  if (page > 1) kb.text("上一页", `referrals_page:${page - 1}`);
  if (page * limit < total) kb.text("下一页", `referrals_page:${page + 1}`);
  await ctx.editMessageText(text, { reply_markup: kb });
});

bot.callbackQuery("admin_dm_verify", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  adminDmVerifyMode.set(ctx.from.id, true);
  await ctx.reply("请发送需要私聊的用户名（例如 @username），或发送用户ID");
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery(/guarantor:(\w+)/, async (ctx) => {
  const choice = (ctx.match[1] || "").toLowerCase();
  const uid = ctx.from?.id || 0;
  const jr = userJoinRequestState.get(uid);
  if (!jr || jr.step !== "await_guarantor") {
    await ctx.answerCallbackQuery({ text: "状态无效或已提交", show_alert: false });
    return;
  }
  setJoinRequestGuarantor(jr.chatId, uid, choice);
  userJoinRequestState.delete(uid);
  try {
    await ctx.editMessageText("申请已经提交 等待数据库核验");
  } catch {}
  await ctx.answerCallbackQuery({ text: "✅ 已提交" });
});

bot.on("chat_member", async (ctx) => {
  const u = ctx.update.chat_member;
  const il = u.invite_link;
  if (!il) return;
  const link = il.invite_link || il;
  const row = getInviteByLink(link);
  if (!row) return;
  const inviterId = row.inviter_id;
  const inviteeId = u.from?.id || 0;
  const chatId = u.chat?.id || 0;
  const status = u.new_chat_member?.status;
  if (status === "member" || status === "administrator") {
    addReferral(chatId, inviterId, inviteeId, link);
    try {
      await bot.api.sendMessage(inviterId, `你邀请的用户 ${inviteeId} 已加入`);
    } catch {}
  }
});

bot.hears(/^我的邀请链接$/, async (ctx) => {
  if (!ctx.chat || !(ctx.chat.type === "group" || ctx.chat.type === "supergroup")) return;
  const uid = ctx.from?.id || 0;
  const chatId = ctx.chat.id;
  try {
    const name = `inv_${uid}_${Date.now()}`;
    const link = await bot.api.createChatInviteLink(chatId, { name, creates_join_request: true });
    addInviteLink(chatId, uid, link.invite_link, name);
    await ctx.reply(`你的邀请链接：\n${link.invite_link}`, { reply_to_message_id: ctx.message.message_id });
  } catch (e) {
    await ctx.reply("无法生成邀请链接，请确保机器人在该群是管理员并具有创建邀请链接权限");
  }
});

bot.hears(/^\/?id$/i, async (ctx) => {
  if (!ctx.chat || !(ctx.chat.type === "group" || ctx.chat.type === "supergroup")) return;
  const uid = ctx.from?.id || 0;
  await ctx.reply(`你的Telegram ID: ${uid}`, { reply_to_message_id: ctx.message.message_id });
});

bot.hears(/^开始圣诞节活动$/, async (ctx) => {
  if (!ctx.chat || !(ctx.chat.type === "group" || ctx.chat.type === "supergroup")) return;
  const uid = ctx.from?.id || 0;
  if (!uid || !isAdmin(uid)) return;
  try {
    if (!BOT_USERNAME) {
      const me = await bot.api.getMe();
      BOT_USERNAME = me.username || "";
    }
    const chatId = ctx.chat.id;
    const url = BOT_USERNAME ? `https://t.me/${BOT_USERNAME}?start=christmas_${chatId}` : undefined;
    const kb = new InlineKeyboard();
    if (url) kb.url("🎄 点击许愿参与", url);
    const text = "圣诞节抽奖活动开始啦 🎁\n开奖时间：12月25日 20:00\n请点击下方按钮进入机器人进行许愿";
    await ctx.reply(text, { reply_markup: kb });
  } catch {
    await ctx.reply("活动入口生成失败");
  }
});

bot.hears(/^我的愿望$/, async (ctx) => {
  const uid = ctx.from?.id || 0;
  if (!uid) return;
  if (ctx.chat?.type === "group" || ctx.chat?.type === "supergroup") {
    const row = getChristmasWish(ctx.chat.id, uid);
    if (row && typeof row.wish_text === "string" && row.wish_text.length) {
      await ctx.reply(`你的愿望：${row.wish_text}`, { reply_to_message_id: ctx.message.message_id });
    } else {
      await ctx.reply("未找到你的愿望");
    }
    return;
  }
  const last = getLatestChristmasWish(uid);
  if (last && typeof last.wish_text === "string" && last.wish_text.length) {
    await ctx.reply(`你最近的愿望：${last.wish_text}\n群ID：${last.chat_id}`);
  } else {
    await ctx.reply("未找到你的愿望");
  }
});

bot.on("chat_join_request", async (ctx) => {
  const u = ctx.update.chat_join_request;
  if (!u) return;
  const userId = u.from?.id || 0;
  const chatId = u.chat?.id || 0;
  const title = u.chat?.title || "群组";
  const link = u.invite_link?.invite_link || "";
  ensureJoinRequest(chatId, userId, link);
  const nonce = crypto.randomBytes(8).toString("hex");
  userJoinRequestState.set(userId, { chatId, deadline: Date.now() + 24 * 60 * 60 * 1000, step: "await_verify", nonce });
  try {
    const kb = new InlineKeyboard().text("开始人机验证", `verify_join:${chatId}:${userId}:${nonce}`);
    await bot.api.sendMessage(userId, `你正在申请加入 ${title}\n请点击下方按钮进行人机验证，验证通过将自动审核进入`, { reply_markup: kb });
  } catch {}
});

bot.callbackQuery(/verify_join:(-?\d+):(\d+):([a-f0-9]+)/, async (ctx) => {
  try { await ctx.answerCallbackQuery(); } catch {}
  const chatId = parseInt(ctx.match[1]);
  const userId = parseInt(ctx.match[2]);
  const nonce = ctx.match[3];
  const st = userJoinRequestState.get(userId);
  if (!st || st.chatId !== chatId || st.nonce !== nonce || st.step !== "await_verify") {
    try { await ctx.answerCallbackQuery({ text: "验证状态无效或已过期", show_alert: true }); } catch {}
    return;
  }
  if (Date.now() > st.deadline) {
    userJoinRequestState.delete(userId);
    try { await ctx.editMessageText("验证已过期，请重新申请"); } catch {}
    return;
  }
  // 生成简单人机验证题目（点击指定数字）
  const digits = ["1","2","3","4","5"];
  const answer = digits[Math.floor(Math.random() * digits.length)];
  userCaptchaState.set(userId, { chatId, nonce, answer, expires: Date.now() + 60_000, attempts: 0 });
  setJoinRequestStatus(chatId, userId, "await_captcha");
  const kb = new InlineKeyboard()
    .text("1", `captcha_ans:${chatId}:${userId}:${nonce}:1`)
    .text("2", `captcha_ans:${chatId}:${userId}:${nonce}:2`)
    .row()
    .text("3", `captcha_ans:${chatId}:${userId}:${nonce}:3`)
    .text("4", `captcha_ans:${chatId}:${userId}:${nonce}:4`)
    .row()
    .text("5", `captcha_ans:${chatId}:${userId}:${nonce}:5`);
  try {
    await ctx.editMessageText(`人机验证：请点击数字 ${answer}`, { reply_markup: kb });
  } catch {
    try { await ctx.reply(`人机验证：请点击数字 ${answer}`, { reply_markup: kb }); } catch {}
  }
});

bot.callbackQuery(/captcha_ans:(-?\d+):(\d+):([a-f0-9]+):(\d)/, async (ctx) => {
  try { await ctx.answerCallbackQuery(); } catch {}
  const chatId = parseInt(ctx.match[1]);
  const userId = parseInt(ctx.match[2]);
  const nonce = ctx.match[3];
  const choice = ctx.match[4];
  const st = userCaptchaState.get(userId);
  if (!st || st.chatId !== chatId || st.nonce !== nonce) {
    try { await ctx.answerCallbackQuery({ text: "验证状态无效或已过期", show_alert: true }); } catch {}
    return;
  }
  if (Date.now() > st.expires) {
    userCaptchaState.delete(userId);
    userJoinRequestState.delete(userId);
    setJoinRequestStatus(chatId, userId, "expired");
    try { await ctx.editMessageText("验证已过期，请重新申请"); } catch {}
    return;
  }
  if (choice === st.answer) {
    try {
      setJoinRequestStatus(chatId, userId, "verified");
      await bot.api.approveChatJoinRequest(chatId, userId);
      userCaptchaState.delete(userId);
      userJoinRequestState.delete(userId);
      try { await ctx.editMessageText("验证通过，已自动审核进入"); } catch {}
    } catch (e) {
      try { await ctx.answerCallbackQuery({ text: "审批失败，请稍后重试", show_alert: true }); } catch {}
    }
    return;
  } else {
    st.attempts += 1;
    if (st.attempts >= 3) {
      userCaptchaState.delete(userId);
      userJoinRequestState.delete(userId);
      setJoinRequestStatus(chatId, userId, "blocked");
      try { await bot.api.declineChatJoinRequest(chatId, userId); } catch {}
      try { await ctx.editMessageText("验证失败次数过多，已拒绝申请"); } catch {}
      return;
    }
    // 再次生成新题
    const digits = ["1","2","3","4","5"];
    const answer = digits[Math.floor(Math.random() * digits.length)];
    st.answer = answer;
    st.expires = Date.now() + 60_000;
    userCaptchaState.set(userId, st);
    const kb = new InlineKeyboard()
      .text("1", `captcha_ans:${chatId}:${userId}:${nonce}:1`)
      .text("2", `captcha_ans:${chatId}:${userId}:${nonce}:2`)
      .row()
      .text("3", `captcha_ans:${chatId}:${userId}:${nonce}:3`)
      .text("4", `captcha_ans:${chatId}:${userId}:${nonce}:4`)
      .row()
      .text("5", `captcha_ans:${chatId}:${userId}:${nonce}:5`);
    try { await ctx.editMessageText(`错误，请重试：请点击数字 ${answer}`, { reply_markup: kb }); } catch {}
    return;
  }
});

// 提取文件解析逻辑
function extractSessionsFromFile(filePath, originalName) {
  const sessionsToTest = [];
  const isTxt = originalName.endsWith(".txt");
  const isSession = originalName.endsWith(".session");
  const isZip = originalName.endsWith(".zip");
  const isJson = originalName.endsWith(".json");
  
  const dcOptions = { 
    1: "149.154.175.53:443", 
    2: "149.154.167.50:443", 
    3: "149.154.175.100:443", 
    4: "149.154.167.91:443", 
    5: "91.108.56.130:443" 
  };

  if (isJson) {
      console.log(`[Import] Processing .json file: ${originalName}`);
      try {
        const content = fs.readFileSync(filePath, "utf-8");
        console.log(`[Import] Content preview: ${content.substring(0, 100)}...`);
        const obj = JSON.parse(content);
        
        // 递归查找可能的 session string 或 session 对象
        const findSession = (o) => {
          if (!o) return;
          
          // 1. 直接是字符串
          if (typeof o === 'string') {
            const s = o.trim();
            // 放宽正则：允许 - _，长度 > 20
            if (s.length > 20 && /^[a-zA-Z0-9+/=_ -]+$/.test(s)) {
              sessionsToTest.push(s);
            }
            return;
          }
          
          // 2. 是对象
          if (typeof o === 'object') {
             // 检查是否包含 session 构造字段 (dcId + authKey)
             if (o.dcId && o.authKey) {
                const dcId = Number(o.dcId);
                const addr = dcOptions[dcId];
                if (addr && typeof o.authKey === 'string') {
                   try {
                     // 尝试 hex 或 base64 解码
                     let keyBuf;
                     if (/^[0-9a-fA-F]+$/.test(o.authKey)) keyBuf = Buffer.from(o.authKey, 'hex');
                     else keyBuf = Buffer.from(o.authKey, 'base64');
                     
                     if (keyBuf.length === 256) {
                        const [ip, portStr] = addr.split(":");
                        const s = new StringSession("");
                        s._dcId = dcId;
                        s._serverAddress = ip;
                        s._port = parseInt(portStr);
                        s._authKey = new (require("telegram/crypto/AuthKey").AuthKey)();
                        s._authKey.setKey(keyBuf);
                        // 如果有 apiId/hash，优先使用
                        const res = { session: s.save() };
                        if (o.appId || o.apiId) res.apiId = parseInt(o.appId || o.apiId);
                        if (o.appHash || o.apiHash) res.apiHash = String(o.appHash || o.apiHash);
                        
                        sessionsToTest.push(res);
                        return; // 已找到并转换，跳过子属性
                     }
                   } catch(e) { console.error("Construct session failed", e); }
                }
             }
          
             // 优先检查常见字段名
             const keys = Object.keys(o);
             for (const k of keys) {
               const lk = k.toLowerCase();
               if (lk === 'session' || lk === 'session_string' || lk === 'string_session' || lk === 'data') {
                  if (typeof o[k] === 'string') {
                    const s = o[k].trim();
                    if (s.length > 20 && /^[a-zA-Z0-9+/=_ -]+$/.test(s)) {
                       // 尝试寻找同级或上级的 api_id/hash
                       const res = { session: s };
                       if (o.appId || o.apiId) res.apiId = parseInt(o.appId || o.apiId);
                       if (o.appHash || o.apiHash) res.apiHash = String(o.appHash || o.apiHash);
                       sessionsToTest.push(res);
                       continue; 
                    }
                  }
               }
               findSession(o[k]);
             }
          }
        };
        findSession(obj);
      } catch (e) {
        console.error(`[Import] JSON parse error: ${e.message}`);
      }
  } else if (isZip) {
      console.log(`[Import] Processing ZIP file: ${originalName}`);
      try {
        const zip = new AdmZip(filePath);
        const zipEntries = zip.getEntries();
        for (const entry of zipEntries) {
          if (entry.isDirectory) continue;
          const entryName = entry.entryName;
          const lowerName = entryName.toLowerCase();
          
          // 处理 .json 文件
          if (lowerName.endsWith(".json")) {
             try {
                const content = zip.readAsText(entry);
                const obj = JSON.parse(content);
                // 复用 JSON 提取逻辑
                // 这里简单处理：递归查找 session
                const findSession = (o) => {
                  if (!o) return;
                  if (typeof o === 'string') {
                    const s = o.trim();
                    if (s.length > 20 && /^[a-zA-Z0-9+/=_ -]+$/.test(s)) {
                       // 尝试在同级找 api_id
                       const res = { session: s };
                       // 这是一个简化的假设，如果 session 是字符串，可能 api_id 在父级对象里
                       // 但这里的 o 是字符串，无法访问父级。
                       // 所以对于纯字符串，我们只存 session。
                       sessionsToTest.push(res);
                    }
                    return;
                  }
                  if (typeof o === 'object') {
                     // 检查常见字段
                     if (o.session || o.session_string || o.data) {
                        const s = (o.session || o.session_string || o.data || "").trim();
                        if (s.length > 20) {
                           const res = { session: s };
                           if (o.appId || o.apiId) res.apiId = parseInt(o.appId || o.apiId);
                           if (o.appHash || o.apiHash) res.apiHash = String(o.appHash || o.apiHash);
                           sessionsToTest.push(res);
                           return;
                        }
                     }
                     Object.values(o).forEach(findSession);
                  }
                };
                findSession(obj);
             } catch(e) {}
          }
          // 处理 .txt/.session 或无后缀文件
          else if (lowerName.endsWith(".txt") || lowerName.endsWith(".session") || !lowerName.includes(".")) {
             try {
                 const content = zip.readAsText(entry);
                 const lines = content.split(/\r?\n/);
                 for (const line of lines) {
                   const l = line.trim();
                   if (l.length > 20 && /^[a-zA-Z0-9+/=]+$/.test(l)) {
                     sessionsToTest.push(l);
                   }
                 }
             } catch(e) {}
          }
        }
      } catch (e) {
        console.error(`[Import] ZIP extract error: ${e.message}`);
      }
  } else if (isSession) {
      console.log(`[Import] Processing .session file: ${originalName}`);
      let extracted = false;
      // 尝试作为 SQLite 读取
      try {
        const sdb = new Database(filePath, { readonly: true, fileMustExist: true });
        try {
          const row = sdb.prepare("SELECT * FROM sessions").get();
          if (row) {
             const dcId = row.dc_id;
             const authKey = row.auth_key; 
             const dcOptions = { 1: "149.154.175.53:443", 2: "149.154.167.50:443", 3: "149.154.175.100:443", 4: "149.154.167.91:443", 5: "91.108.56.130:443" };
             const addr = dcOptions[dcId];
             if (addr && authKey && authKey.length === 256) {
                const [ip, portStr] = addr.split(":");
                const port = parseInt(portStr);
                const s = new StringSession("");
                s._dcId = dcId;
                s._serverAddress = ip;
                s._port = port;
                s._authKey = new (require("telegram/crypto/AuthKey").AuthKey)();
                s._authKey.setKey(authKey);
                sessionsToTest.push(s.save());
                extracted = true;
             }
          }
        } catch(e) {}
        sdb.close();
      } catch (e) {}
      
      if (!extracted) {
        try {
          const content = fs.readFileSync(filePath, "utf-8");
          const lines = content.split(/\r?\n/);
          for (const line of lines) {
            const l = line.trim();
            if (l.length > 20 && /^[a-zA-Z0-9+/=]+$/.test(l)) sessionsToTest.push(l);
          }
        } catch (e) {}
      }
  } else {
      // .txt or others
      console.log(`[Import] Processing text file: ${originalName}`);
      try {
          const content = fs.readFileSync(filePath, "utf-8");
          if (content.startsWith("PK")) {
             try {
                const zip = new AdmZip(filePath);
                const zipEntries = zip.getEntries();
                for (const entry of zipEntries) {
                  if (entry.isDirectory) continue;
                  const c = zip.readAsText(entry);
                  const lines = c.split(/\r?\n/);
                  for (const line of lines) {
                    const l = line.trim();
                    if (l.length > 20 && /^[a-zA-Z0-9+/=]+$/.test(l)) sessionsToTest.push(l);
                  }
                }
             } catch(e) {}
          } else {
              const lines = content.split(/\r?\n/);
              for (const line of lines) {
                // 移除可能的 JSON 引号和逗号
                let l = line.trim();
                if (l.startsWith('"') && l.endsWith('",')) l = l.slice(1, -2);
                else if (l.startsWith('"') && l.endsWith('"')) l = l.slice(1, -1);
                
                if (l.length > 20 && /^[a-zA-Z0-9+/=]+$/.test(l)) sessionsToTest.push(l);
              }
          }
      } catch(e) {}
  }
  return sessionsToTest;
}

// const userWebLoginState = new Map(); // Removed duplicate declaration
function parseCookies(req) {
  const list = {};
  const rc = req.headers.cookie;
  if (rc) {
    rc.split(";").forEach((cookie) => {
      const parts = cookie.split("=");
      list[parts.shift().trim()] = decodeURI(parts.join("="));
    });
  }
  return list;
}

function createSession(username) {
  const token = crypto.randomBytes(16).toString("hex");
  addWebSession(token, username); // 使用 DB 持久化
  return token;
}

async function boot() {
  try {
    await bot.api.deleteWebhook({ drop_pending_updates: false });
  } catch (e) {
    console.error("Webhook delete error", e);
  }
  try {
    if (hasBackup() && countPosts() === 0) {
      restorePostsFromBackup();
      console.log("Restored posts from backup");
    }
  } catch (e) {}
  try {
    const WEB_ADMIN_USER = process.env.ADMIN_WEB_USER || "aj999aj";
    const WEB_ADMIN_PASS = process.env.ADMIN_WEB_PASS || "wanan1314";
    ensureWebAdmin(WEB_ADMIN_USER, WEB_ADMIN_PASS);
    console.log(`[WebAdmin] Ensure admin user: ${WEB_ADMIN_USER}`);
  } catch (e) {}
  try {
    const WEB_PORT = process.env.PORT ? Number(process.env.PORT) : (process.env.WEB_PORT ? Number(process.env.WEB_PORT) : 3000);
    const htmlPath = path.join(__dirname, "..", "public", "index.html");
    const adminPath = path.join(__dirname, "..", "public", "admin.html");
    const server = http.createServer((req, res) => {
      // API: Generate QR Token
      if (req.method === "POST" && req.url === "/api/telegram/login/qr") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false, error: "Unauthorized" }));
          return;
        }
        
        const token = crypto.randomBytes(16).toString("hex");
        addQrToken(token);
        
        res.writeHead(200, { "Content-Type": "application/json" });
        res.end(JSON.stringify({ ok: true, token, botUsername: bot.botInfo.username }));
        return;
      }

      // API: Check QR Status
      if (req.method === "POST" && req.url === "/api/telegram/login/check") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false, error: "Unauthorized" }));
          return;
        }
        let body = "";
        req.on("data", (c) => body += c);
        req.on("end", async () => {
          try {
            const { token } = JSON.parse(body || "{}");
            if (!token) throw new Error("Missing token");
            
            const row = getQrToken(token);
            if (!row) {
              res.writeHead(200, { "Content-Type": "application/json" });
              res.end(JSON.stringify({ ok: false, error: "Expired" }));
              return;
            }
            
            if (row.session) {
              // 验证 session 并入库
              const { apiId, apiHash } = getCurrentApiConfig();
              const client = new TelegramClient(new StringSession(row.session), parseInt(apiId), String(apiHash), { 
                  connectionRetries: 1, 
                  useWSS: false 
              });
              await client.connect();
              const me = await client.getMe();
              if (me) {
                 addAccount(me.phone || me.id.toString(), me.phone || me.id.toString(), row.session, {
                    telegramId: me.id,
                    username: me.username || "",
                    firstName: me.firstName || "",
                    lastName: me.lastName || ""
                 });
                 deleteQrToken(token);
                 await client.disconnect();
                 
                 res.writeHead(200, { "Content-Type": "application/json" });
                 res.end(JSON.stringify({ ok: true }));
              } else {
                 await client.disconnect();
                 res.writeHead(200, { "Content-Type": "application/json" });
                 res.end(JSON.stringify({ ok: false, error: "Invalid session" }));
              }
            } else {
              res.writeHead(200, { "Content-Type": "application/json" });
              res.end(JSON.stringify({ ok: false, pending: true }));
            }
          } catch (e) {
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: false, error: e.message }));
          }
        });
        return;
      }

      // API: Web Login (Send Code)
      if (req.method === "POST" && req.url === "/api/telegram/login/send-code") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false, error: "Unauthorized" }));
          return;
        }
        let body = "";
        req.on("data", (c) => body += c);
        req.on("end", async () => {
          try {
            let { phone } = JSON.parse(body || "{}");
            if (!phone) throw new Error("请输入手机号");
            
            // 格式化手机号：去除空格，确保 + 开头
            phone = phone.replace(/\s+/g, "");
            if (!phone.startsWith("+")) phone = "+" + phone;
            
            const { apiId, apiHash } = getCurrentApiConfig();
            if (!apiId || !apiHash) throw new Error("API配置无效");
            
            // 强制类型转换
            const finalApiId = parseInt(apiId);
            const finalApiHash = String(apiHash);

            const client = new TelegramClient(new StringSession(""), finalApiId, finalApiHash, { 
              connectionRetries: 5,
              deviceModel: "Desktop", // 伪装成桌面端
              appVersion: "4.16.8 x64",
              systemVersion: "Windows 10",
              useWSS: false,
            });
            await client.connect();
            
            // 尝试获取最新配置以更新 DC
            try { 
                const config = await client.invoke(new Api.help.GetConfig()); 
                console.log(`[WebLogin] Connected to DC ${config.thisDc}`);
            } catch (e) {
                console.log(`[WebLogin] GetConfig failed: ${e.message}`);
            }
            
            // 使用底层 invoke 直接调用 auth.SendCode
            console.log(`[WebLogin] Sending code to ${phone} with ID: ${finalApiId}`);
            const result = await client.invoke(new Api.auth.SendCode({
              phoneNumber: phone,
              apiId: finalApiId,
              apiHash: finalApiHash,
              settings: new Api.CodeSettings({
                allowFlashcall: false,
                currentNumber: false,
                allowAppHash: false
              })
            }));
            
            console.log(`[WebLogin] Code sent. Hash length: ${result.phoneCodeHash ? result.phoneCodeHash.length : 0}`);
            const phoneCodeHash = result.phoneCodeHash;
            
            userWebLoginState.set(tok, { client, phone, phoneCodeHash });
            
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: true }));
          } catch (e) {
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: false, error: e.message }));
          }
        });
        return;
      }
      
      // API: Web Login (Sign In)
      if (req.method === "POST" && req.url === "/api/telegram/login/sign-in") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        const state = userWebLoginState.get(tok);
        if (!tok || !session || !state) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false, error: "Session expired or invalid state" }));
          return;
        }
        let body = "";
        req.on("data", (c) => body += c);
        req.on("end", async () => {
          try {
            const { code } = JSON.parse(body || "{}");
            if (!code) throw new Error("请输入验证码");
            
            await state.client.invoke(new Api.auth.SignIn({
              phoneNumber: state.phone,
              phoneCodeHash: state.phoneCodeHash,
              phoneCode: code.toString(),
            }));
            
            // Success
            const session = state.client.session.save();
            const me = await state.client.getMe();
            addAccount(me.phone || state.phone, me.phone || state.phone, session, {
              telegramId: me.id,
              username: me.username || "",
              firstName: me.firstName || "",
              lastName: me.lastName || ""
            });
            await state.client.disconnect();
            userWebLoginState.delete(tok);
            
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: true, user: { id: me.id, firstName: me.firstName, phone: me.phone } }));
          } catch (e) {
            if (e.message.includes("SESSION_PASSWORD_NEEDED")) {
              res.writeHead(200, { "Content-Type": "application/json" });
              res.end(JSON.stringify({ ok: false, error: "2FA_REQUIRED" }));
            } else {
              res.writeHead(200, { "Content-Type": "application/json" });
              res.end(JSON.stringify({ ok: false, error: e.message }));
            }
          }
        });
        return;
      }
      
      // API: Web Login (2FA)
      if (req.method === "POST" && req.url === "/api/telegram/login/2fa") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        const state = userWebLoginState.get(tok);
        if (!tok || !session || !state) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false, error: "Session expired" }));
          return;
        }
        let body = "";
        req.on("data", (c) => body += c);
        req.on("end", async () => {
          try {
            const { password } = JSON.parse(body || "{}");
            if (!password) throw new Error("请输入密码");
            
            // 手动构建 checkPassword 请求
            // 1. 获取当前账号的 password info
            const pwdInfo = await state.client.invoke(new Api.account.GetPassword());
            
            // 2. 计算 SRP hash
            const { computeCheck } = require("telegram/Password");
            const { A, M1 } = await computeCheck(pwdInfo, password);
            
            // 3. 发送 checkPassword
            await state.client.invoke(new Api.auth.CheckPassword({
              password: new Api.InputCheckPasswordSRP({
                srpId: pwdInfo.srpId,
                A: A,
                M1: M1
              })
            }));
            
            // Success
            const session = state.client.session.save();
            const me = await state.client.getMe();
            addAccount(me.phone || state.phone, session);
            await state.client.disconnect();
            userWebLoginState.delete(tok);
            
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: true, user: { id: me.id, firstName: me.firstName, phone: me.phone } }));
          } catch (e) {
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: false, error: e.message }));
          }
        });
        return;
      }

      // API: Check Accounts
      if (req.method === "POST" && req.url === "/api/telegram/accounts/check") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false }));
          return;
        }
        
        // 异步执行检查，不阻塞响应
        (async () => {
           const accounts = getAllAccounts();
           const { apiId, apiHash } = getCurrentApiConfig();
           const globalApiId = parseInt(apiId);
           const globalApiHash = String(apiHash);
           
           for (const acc of accounts) {
             if (!acc.session) continue;
             try {
               const client = new TelegramClient(new StringSession(acc.session), globalApiId, globalApiHash, { 
                  connectionRetries: 1, 
                  useWSS: false 
               });
               await client.connect();
               const me = await client.getMe();
               if (me) {
                 // 修正状态和信息
                 addAccount(me.phone || me.id.toString(), acc.session, {
                    telegramId: me.id,
                    username: me.username || "",
                    firstName: me.firstName || "",
                    lastName: me.lastName || ""
                 });
               } else {
                 setAccountStatus(acc.phone, "invalid");
               }
               await client.disconnect();
             } catch (e) {
               console.error(`Check account ${acc.phone} failed:`, e.message);
               if (e.message.includes("AUTH_KEY_UNREGISTERED") || e.message.includes("SESSION_REVOKED")) {
                  setAccountStatus(acc.phone, "invalid");
               }
             }
           }
        })();
        
        res.writeHead(200, { "Content-Type": "application/json" });
        res.end(JSON.stringify({ ok: true, message: "检查任务已在后台启动，请稍后刷新" }));
        return;
      }

      // API: List Accounts
      if (req.method === "GET" && req.url === "/api/telegram/accounts") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false }));
          return;
        }
        const list = listAccounts();
        // 隐藏 session 详情，只返回基本信息
        const safeList = list.map(a => ({ 
          phone: a.phone, 
          status: a.status === 'ok' ? '在线' : (a.status === 'pending' ? '等待验证' : a.status), 
          updatedAt: a.updated_at,
          telegramId: a.telegram_id,
          username: a.username,
          firstName: a.first_name,
          lastName: a.last_name
        }));
        res.writeHead(200, { "Content-Type": "application/json" });
        res.end(JSON.stringify({ ok: true, list: safeList }));
        return;
      }

      // API: Get Business Anti Edit/Delete
      if (req.method === "GET" && req.url === "/api/business/anti") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false }));
          return;
        }
        const enabled = getBusinessAntiEditDelete();
        res.writeHead(200, { "Content-Type": "application/json" });
        res.end(JSON.stringify({ ok: true, enabled }));
        return;
      }

      // API: Set Business Anti Edit/Delete
      if (req.method === "POST" && req.url === "/api/business/anti") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false }));
          return;
        }
        let body = "";
        req.on("data", (c) => body += c);
        req.on("end", () => {
          try {
            let payload = {};
            try { payload = JSON.parse(body || "{}"); } catch {}
            const current = getBusinessAntiEditDelete();
            const next = typeof payload.enabled === "boolean" ? payload.enabled : (!current);
            setBusinessAntiEditDelete(next);
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: true, enabled: next }));
          } catch (e) {
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: false, error: e.message }));
          }
        });
        return;
      }

      // API: Import Sessions (File Upload)
      if (req.method === "POST" && req.url === "/api/telegram/import") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false, error: "Unauthorized" }));
          return;
        }
        let body = "";
        req.on("data", (c) => body += c);
        req.on("end", async () => {
          try {
            // Body: { filename: string, contentBase64: string }
            // Note: For large files, this JSON approach is not efficient, but sufficient for session files
            const { filename, contentBase64 } = JSON.parse(body || "{}");
            if (!filename || !contentBase64) throw new Error("Missing file data");
            
            const buffer = Buffer.from(contentBase64, "base64");
            const tmpPath = path.join(__dirname, "..", `temp_web_${Date.now()}_${filename}`);
            fs.writeFileSync(tmpPath, buffer);
            
            // Extract sessions
            const sessionsToTest = extractSessionsFromFile(tmpPath, filename);
            fs.unlinkSync(tmpPath); // Delete temp file
            
            if (!sessionsToTest.length) {
              res.writeHead(200, { "Content-Type": "application/json" });
              res.end(JSON.stringify({ ok: false, error: "未找到有效的协议号" }));
              return;
            }
            
            // Validate sessions
            let success = 0;
            let fail = 0;
            let exists = 0;
            const { apiId, apiHash } = getCurrentApiConfig();
            
            // We'll process them in parallel with a limit, or sequential. Sequential is safer for now.
            for (const item of sessionsToTest) {
              try {
                // 优先使用从文件提取的 api_id/hash，否则使用系统默认
                const useApiId = item.apiId || parseInt(apiId);
                const useApiHash = item.apiHash || String(apiHash);
                
                console.log(`[Import] Testing session (API_ID: ${useApiId})...`);
                const client = new TelegramClient(new StringSession(item.session), useApiId, useApiHash, { 
                    connectionRetries: 1, 
                    useWSS: false 
                });
                await client.connect();
                const me = await client.getMe();
                if (me) {
                   const phone = me.phone || me.id.toString();
                   // 检查是否已存在
                   const old = getAccountByPhone(phone);
                   if (old) {
                     exists++;
                   } else {
                     addAccount(phone, phone, item.session, {
                        telegramId: me.id,
                        username: me.username || "",
                        firstName: me.firstName || "",
                        lastName: me.lastName || ""
                     });
                     success++;
                   }
                } else {
                   fail++;
                }
                await client.disconnect();
              } catch (e) {
                console.error("[Import] Verify failed:", e.message);
                fail++;
              }
            }
            
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: true, total: sessionsToTest.length, success, fail, exists }));
          } catch (e) {
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: false, error: e.message }));
          }
        });
        return;
      }
      
      // API: Logout/Delete Account
      if (req.method === "POST" && req.url === "/api/telegram/logout") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok: false }));
          return;
        }
        let body = "";
        req.on("data", (c) => body += c);
        req.on("end", async () => {
          try {
            const { phone } = JSON.parse(body || "{}");
            if (!phone) throw new Error("Missing phone");
            
            // 尝试断开连接（如果能获取到 session）
            const acc = listAccounts().find(a => a.phone === phone);
            if (acc) {
               try {
                 const { apiId, apiHash } = getCurrentApiConfig();
                 const client = new TelegramClient(new StringSession(acc.session_string || acc.session), apiId, apiHash, { connectionRetries: 1 });
                 await client.connect();
                 await client.invoke(new Api.auth.LogOut());
                 await client.disconnect();
               } catch (e) { console.error("Logout error", e); }
            }
            
            deleteAccount(phone);
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: true }));
          } catch (e) {
            res.writeHead(200, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: false, error: e.message }));
          }
        });
        return;
      }
      
      if (req.method === "POST" && req.url === "/api/login") {
        let body = "";
        req.on("data", (c) => body += c);
        req.on("end", () => {
          try {
            let payload = {};
            try { payload = JSON.parse(body || "{}"); } catch {}
            const ok = verifyWebAdmin(payload.username || "", payload.password || "");
            if (!ok) {
              res.writeHead(401, { "Content-Type": "application/json" });
              res.end(JSON.stringify({ ok: false }));
              return;
            }
            const token = createSession(payload.username);
            res.writeHead(200, { "Content-Type": "application/json", "Set-Cookie": `admin_session=${token}; HttpOnly; SameSite=Lax; Path=/` });
            res.end(JSON.stringify({ ok: true }));
          } catch (e) {
            console.error("[Login Error]", e);
            res.writeHead(500, { "Content-Type": "application/json" });
            res.end(JSON.stringify({ ok: false, error: e.message }));
          }
        });
        return;
      }
      if (req.method === "GET" && req.url === "/admin") {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          fs.readFile(htmlPath, (err, data) => {
            if (err) { res.statusCode = 500; res.end("error"); return; }
            res.setHeader("Content-Type", "text/html; charset=utf-8");
            res.end(data);
          });
          return;
        }
        fs.readFile(adminPath, (err, data) => {
          if (err) { res.statusCode = 500; res.end("error"); return; }
          res.setHeader("Content-Type", "text/html; charset=utf-8");
          res.end(data);
        });
        return;
      }
      if (req.method === "GET" && req.url.startsWith("/api/stats")) {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok:false }));
          return;
        }
        const u = new URL(req.url, `http://${req.headers.host}`);
        const type = u.searchParams.get("type") || "today_income";
        const now = new Date();
        function fmt(d){ const y=d.getFullYear(); const m=(d.getMonth()+1).toString().padStart(2,'0'); const dd=d.getDate().toString().padStart(2,'0'); return `${y}-${m}-${dd}`; }
        function genSeries(days){ const out=[]; for(let i=days-1;i>=0;i--){ const d=new Date(now); d.setDate(d.getDate()-i); out.push({ date: fmt(d), value: Math.round((Math.random()*500+100)*100)/100 }); } return out; }
        let data = { summary:{ income:0, outgoing:0, profit:0 }, series:[] };
        if (type === "today_income") {
          data.series = genSeries(1); data.summary.income = data.series[0].value;
        } else if (type === "today_outgoing") {
          data.series = genSeries(1); data.summary.outgoing = data.series[0].value;
        } else if (type === "last30_profit") {
          data.series = genSeries(30); data.summary.profit = Math.round(data.series.reduce((s,x)=>s+x.value,0)*100)/100;
        } else if (type === "custom") {
          const from = u.searchParams.get("from"); const to = u.searchParams.get("to");
          const df = from ? new Date(from) : new Date(now.getFullYear(), now.getMonth(), now.getDate()-6);
          const dt = to ? new Date(to) : now;
          const days = Math.max(1, Math.ceil((dt - df)/86400000)+1);
          data.series = genSeries(days);
          data.summary.income = Math.round(data.series.reduce((s,x)=>s+x.value,0)*100)/100;
        }
        res.writeHead(200, { "Content-Type": "application/json" });
        res.end(JSON.stringify({ ok:true, data }));
        return;
      }
      if (req.method === "GET" && req.url.startsWith("/api/finance")) {
        const cookies = parseCookies(req);
        const tok = cookies.admin_session;
        const session = getWebSession(tok);
        if (!tok || !session) {
          res.writeHead(401, { "Content-Type": "application/json" });
          res.end(JSON.stringify({ ok:false }));
          return;
        }
        const u = new URL(req.url, `http://${req.headers.host}`);
        const type = u.searchParams.get("type") || "summary";
        const now = new Date();
        function fmt(d){ const y=d.getFullYear(); const m=(d.getMonth()+1).toString().padStart(2,'0'); const dd=d.getDate().toString().padStart(2,'0'); return `${y}-${m}-${dd}`; }
        function genFlows(days){ const out=[]; for(let i=days-1;i>=0;i--){ const d=new Date(now); d.setDate(d.getDate()-i); const v=(Math.random()<.5?-1:1)*Math.round((Math.random()*500+50)*100)/100; out.push({ date: fmt(d), amount: v, type: v>=0?"收入":"支出", desc: v>=0?"订单入账":"渠道出款" }); } return out; }
        function genWithdraws(days){ const out=[]; const statuses=["待审核","通过","驳回"]; for(let i=days-1;i>=0;i--){ const d=new Date(now); d.setDate(d.getDate()-i); const v=Math.round((Math.random()*800+100)*100)/100; const st=statuses[Math.floor(Math.random()*statuses.length)]; out.push({ date: fmt(d), amount: v, status: st }); } return out; }
        let data = {};
        if (type === "summary") {
          data = { withdrawable: Math.round((Math.random()*10000+2000)*100)/100 };
        } else if (type === "flow") {
          const from = u.searchParams.get("from"); const to = u.searchParams.get("to");
          const df = from ? new Date(from) : new Date(now.getFullYear(), now.getMonth(), now.getDate()-14);
          const dt = to ? new Date(to) : now;
          const days = Math.max(1, Math.ceil((dt - df)/86400000)+1);
          data = { list: genFlows(days) };
        } else if (type === "withdraws") {
          const from = u.searchParams.get("from"); const to = u.searchParams.get("to");
          const df = from ? new Date(from) : new Date(now.getFullYear(), now.getMonth(), now.getDate()-14);
          const dt = to ? new Date(to) : now;
          const days = Math.max(1, Math.ceil((dt - df)/86400000)+1);
          data = { list: genWithdraws(days) };
        }
        res.writeHead(200, { "Content-Type": "application/json" });
        res.end(JSON.stringify({ ok:true, data }));
        return;
      }
      if (req.method === "GET") {
        fs.readFile(htmlPath, (err, data) => {
          if (err) { res.statusCode = 500; res.end("error"); return; }
          res.setHeader("Content-Type", "text/html; charset=utf-8");
          res.end(data);
        });
        return;
      }
      res.statusCode = 405; res.end("");
    });
    server.listen(WEB_PORT, "0.0.0.0");
  } catch (e) {}
  try {
    bot.start();
    console.log("Bot started");
  } catch (e) {
    console.error("Start error", e);
  }
}
boot();
const cleanSteps = new Map();
const userModes = new Map();
const userExtractModes = new Map();
const mediaGroups = new Map();

function addMediaGroupPart(ctx, kind, fileId, groupId, captionText) {
  const uid = ctx.from?.id || 0;
  let g = mediaGroups.get(groupId);
  if (!g) {
    g = { items: [], uid, chatId: ctx.chat?.id || 0, mode: userModes.get(uid) || "normal", extract: getGlobalExtractMode(), caption: "", timer: null };
    mediaGroups.set(groupId, g);
  }
  if (!g.caption) {
    const c = captionText || (groupCaptionCache.get(groupId) || "");
    if (c) g.caption = c;
  }
  g.items.push({ kind, fileId });
  if (g.timer) clearTimeout(g.timer);
  g.timer = setTimeout(() => processMediaGroup(groupId), 1500);
}

async function processMediaGroup(groupId) {
  const g = mediaGroups.get(groupId);
  if (!g) return;
  mediaGroups.delete(groupId);
  const mode = g.mode || "normal";
  
  // 强制重新读取当前的提取模式，避免缓存旧值
  const globalMode = getGlobalExtractMode();
  const extract = g.extract || globalMode || "vc";
  
  const target = mode === "news" ? getNewsBinding() : getBinding();
  if (!target || !target.groupId) {
    await bot.api.sendMessage(g.chatId, mode==='news' ? "未绑定新闻频道" : "未绑定后台群");
    return;
  }
  let items = g.items || [];
  
  // 过滤逻辑：
  // v/vc: 仅视频
  // vci/all: 保留视频和图片
  if (extract === "v" || extract === "vc") {
    items = items.filter(it => it.kind === "video");
  }
  // vc 模式：如果有多个视频，随机选取其中一个，仅提取一个
  if (extract === "vc" && items.length > 1) {
    const idx = Math.floor(Math.random() * items.length);
    items = [items[idx]];
  }
  
  // 针对仅视频模式（v/vc），如果所选视频已存在数据库，仅回复一次并终止，不进行任何提取
  if ((extract === "v" || extract === "vc") && items.length) {
    const vid = items.find(it => it.kind === "video");
    if (vid && hasPostByFileId(vid.fileId)) {
      await bot.api.sendMessage(g.chatId, "这个视频已在数据库");
      return;
    }
  }
  
  if (!items.length) {
    await bot.api.sendMessage(g.chatId, "没有可转发的内容（可能已被过滤）");
    return;
  }
  
  const rawCap = g.caption || "";
  const cleaned = sanitizeCaption(rawCap || "");
  const suffix = "\n➖➖➖➖➖➖➖➖\n❤️关注防失联❤️ @hxkpbot\n➖➖➖➖➖➖➖➖";
  // 如果是仅视频模式，不带文案；其他模式（包括all/vci）都带文案
  // 统一加上广告后缀
  const albumCap = extract === "v" ? "" : (cleaned + suffix);
  
  try {
    const chunks = [];
    for (let i = 0; i < items.length; i += 10) chunks.push(items.slice(i, i + 10));
    
    for (let ci = 0; ci < chunks.length; ci++) {
      const chunk = chunks[ci];
      if (chunk.length === 1) {
        const it = chunk[0];
        // 检查视频是否重复
        if (it.kind === "video") {
          // 由于上游没有传入 unique_id，我们暂时用 file_id 查重（hasPostByFileId）
          if (hasPostByFileId(it.fileId)) {
             await bot.api.sendMessage(g.chatId, "这个视频已在数据库");
             continue;
          }
          const cap = ci === 0 ? albumCap : "";
          await enqueueSendVideo(target.groupId, it.fileId, safeCaption(cap), g.uid || 0);
          insertPost(g.uid || 0, it.fileId, rawCap);
        } else {
          const cap = ci === 0 ? albumCap : "";
          await bot.api.sendPhoto(target.groupId, it.fileId, { caption: safeCaption(cap) });
        }
        continue;
      }
      
      // 批量发送时的去重逻辑
      const newMedia = [];
      for (let idx = 0; idx < chunk.length; idx++) {
        const it = chunk[idx];
        if (it.kind === "video") {
          if (hasPostByFileId(it.fileId)) {
             await bot.api.sendMessage(g.chatId, "这个视频已在数据库");
             continue;
          }
          insertPost(g.uid || 0, it.fileId, rawCap);
          newMedia.push({ type: "video", media: it.fileId });
        } else {
          newMedia.push({ type: "photo", media: it.fileId });
        }
      }
      
      if (newMedia.length > 0) {
        // 确保第一个媒体带上 caption（如果是整个组的第一块）
        if (ci === 0) {
           newMedia[0].caption = safeCaption(albumCap);
        }
        await bot.api.sendMediaGroup(target.groupId, newMedia);
      }
    }
    // 发送成功通知
    const notifyText = mode === "news" ? "已按新闻模式转发" : 
                       (extract === "v" ? "已提取视频并转发" : "已提取转发成功");
    await bot.api.sendMessage(g.chatId, notifyText);
  } catch (e) {
    console.error(e);
    await bot.api.sendMessage(g.chatId, "转发失败，请检查绑定目标权限或是否为频道管理员");
  }
}

function sanitizeCaption(text){
  try {
    let t = text || "";
    // 移除链接
    t = t.replace(/https?:\/\/\S+/gi, "");
    // 移除 t.me 链接
    t = t.replace(/(?:https?:\/\/)?t\.me\/\S+/gi, "");
    // 移除 @username
    t = t.replace(/@[_a-zA-Z0-9]{3,}/g, "");
    // 移除各种联系方式前缀及账号
    t = t.replace(/(?:微.?信|微信|wx|VX|v信|Q?Q|qq|tg|telegram|电报|VX)[\s:：]*[\w\-]+/gi, "");
    // 移除长数字串（疑似手机号/QQ号）
    t = t.replace(/\+?\d[\d\-\s]{6,}\d/gi, "");
    // 移除磁力链接前缀
    t = t.replace(/magnet:\S+/gi, "");
    // 保留标签，不再移除
    // t = t.replace(/#[^\s#]{2,}/g, "");
    
    const lines = t.split(/\r?\n/).map(s=>s.trim()).filter(s=>s.length>0);
    // 移除包含特定推广关键词的整行
    const bad = /(订阅|关注|投稿|联系|加我|加v|加VX|频道|群|客服|推广|合作|日期|时间|By|作者|发布|磁力|btih|torrent|广告)/i;
    // 过滤掉包含 bad 关键词的行，以及包含 magnet: 的行
    const cleaned = lines.filter(s=>!bad.test(s) && !/magnet:/i.test(s)).join("\n");
    return cleaned.trim();
  } catch { return text || ""; }
}

function extractHandles(text){
  try {
    const t = (text || "");
    const out = [];
    for (let i = 0; i < t.length; i++) {
      if (t[i] === "@") {
        let j = i + 1;
        let acc = "";
        while (j < t.length && acc.length < 40) {
          const ch = t[j];
          if (ch === " " || ch === "\n" || ch === "\r" || ch === "\t") { j++; continue; }
          if (/[_a-zA-Z0-9]/.test(ch)) { acc += ch; j++; continue; }
          break;
        }
        if (acc.length >= 5) out.push("@" + acc);
      }
    }
    const seen = new Set();
    return out.filter(n=>{ if(seen.has(n)) return false; seen.add(n); return true; });
  } catch { return []; }
}

function extractHandlesFromLines(text){
  try {
    const lines = (text||"").split(/\r?\n/).map(s=>s.trim()).filter(Boolean);
    const out = [];
    lines.forEach(s=>{
      const found = extractHandles(s);
      if (found.length) { found.forEach(x=>out.push(x)); return; }
      if (/^[_a-zA-Z0-9]{5,}$/.test(s)) out.push("@"+s);
    });
    const seen = new Set();
    return out.filter(n=>{ if(seen.has(n)) return false; seen.add(n); return true; });
  } catch { return []; }
}

function safeCaption(text) {
  try {
    const t = (text || "").trim();
    if (t.length <= 1024) return t;
    return t.slice(0, 1024);
  } catch { return (text || "").slice(0, 1024); }
}

async function saveNamesWithDup(userId, names) {
  const uniq = [];
  const dups = [];
  const seen = new Set();
  for (const n of names) {
    const t = (n || "").trim();
    if (!t) continue;
    if (seen.has(t)) continue;
    seen.add(t);
    if (hasUsername(t)) dups.push(t);
    else uniq.push(t);
  }
  const saved = uniq.length ? addUsernames(userId, uniq) : 0;
  let message = "";
  if (saved > 0) message = `已保存 ${saved} 个用户名`;
  if (dups.length) message = message ? (message + `；已存在：${dups.join(", ")}`) : `这个用户名已在数据库：${dups.join(", ")}`;
  return { saved, duplicates: dups, message };
}

// 已移除 OCR 相关辅助函数

bot.on("message:text", async (ctx) => {
  if (ctx.chat?.type === "private" && ctx.from && userUploadMode.get(ctx.from.id)) {
    const raw = (ctx.update.message.text || "").trim();
    const names = extractHandles(raw);
    if (names.length) {
      const res = await saveNamesWithDup(ctx.from.id, names);
      await ctx.reply(res.message);
      userUploadMode.delete(ctx.from.id);
    } else {
      await ctx.reply("未检测到用户名，请按行发送");
    }
    return;
  }
  if (ctx.chat?.type === "private" && ctx.from) {
    const raw = (ctx.update.message.text || "").trim();
    if (isAdmin(ctx.from.id)) {
      const mDel = raw.match(/^删除\s*@?([_a-zA-Z0-9]{5,})$/);
      if (mDel) {
        const handle = "@" + mDel[1];
        const removed = deleteUsername(handle);
        if (removed > 0) await ctx.reply(`已删除用户名：${handle}`);
        else await ctx.reply("这个吊毛估计是没有注册过机器人");
        return;
      }
    }
    if (!raw || raw.startsWith("/")) return;
    const names = extractHandlesFromLines(raw);
    if (names.length) {
      const res = await saveNamesWithDup(ctx.from.id, names);
      if (res.saved > 0 || res.duplicates.length) await ctx.reply(res.message);
      return;
    }
  }
  if (!ctx.from || !isAdmin(ctx.from.id)) return;
  if (ctx.chat?.type !== "private") return;
  const raw = (ctx.update.message.text || "").trim();
  const forward = ctx.update.message.forward_from_chat;
  let candidate = null;
  if (forward && forward.type === "channel") {
    candidate = { id: forward.id, title: forward.title || "未命名频道" };
  } else {
    const mId = raw.match(/-100\d{5,}/);
    const mAt = raw.match(/@[_a-zA-Z0-9]{5,}/);
    const mUrl = raw.match(/(?:https?:\/\/)?t\.me\/([_a-zA-Z0-9]{5,})/i);
    const target = mId ? mId[0] : (mAt ? mAt[0] : (mUrl ? "@"+mUrl[1] : null));
    if (!target) return;
    try {
      const chat = await ctx.api.getChat(target);
      if (chat.type !== "channel") { await ctx.reply("不是频道"); return; }
      candidate = { id: chat.id, title: chat.title || "未命名频道" };
    } catch (e) { await ctx.reply("绑定失败：未找到该频道"); return; }
  }
  try {
    try { const me = await ctx.api.getMe(); await ctx.api.getChatMember(candidate.id, me.id); } catch {}
    setNewsBinding(candidate.id, candidate.title);
    await ctx.reply(`已绑定新闻频道：${candidate.title}`);
  } catch (e) {
    await ctx.reply("绑定失败，请检查频道ID或机器人是否在该频道");
  }
});
bot.callbackQuery("bind_news_info", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.answerCallbackQuery({ text: "没有权限", show_alert: true }); return; }
  const b = getNewsBinding();
  const kb = new InlineKeyboard().text("返回", "back_home");
  if (b && b.groupId) {
    await ctx.editMessageText(`已绑定新闻频道：${b.groupTitle}`, { reply_markup: kb });
  } else {
    await ctx.editMessageText("当前没有绑定新闻频道，请到目标频道发送 /绑定新闻频道", { reply_markup: kb });
  }
  await ctx.answerCallbackQuery({ text: "✅" });
});

async function ensureBusinessOwner(bizId) {
  try {
    const cached = businessConnections.get(bizId);
    if (cached && cached.userId) return cached.userId;
    const info = await bot.api.getBusinessConnection({ business_connection_id: bizId });
    if (info && info.user) {
      const userId = info.user.id;
      businessConnections.set(bizId, { userId, canReply: info.can_reply, isEnabled: info.is_enabled });
      return userId;
    }
  } catch {}
  return null;
}

async function notifyBusinessOwner(bizId, text) {
  try {
    const uid = await ensureBusinessOwner(bizId);
    if (!uid) return;
    await bot.api.sendMessage(uid, text);
  } catch {}
}

function cacheBusinessMessage(msg) {
  try {
    if (!msg || !msg.chat || !msg.message_id) return;
    const key = `${msg.chat.id}:${msg.message_id}`;
    const from = msg.from ? (msg.from.username ? `@${msg.from.username}` : (msg.from.first_name || "")) : "";
    const content = msg.text || msg.caption || "";
    businessMessageCache.set(key, { from, content });
  } catch {}
}

bot.use(async (ctx, next) => {
  const upd = ctx.update;
  if (upd && upd.business_connection) {
    try {
      const bc = upd.business_connection;
      const id = bc.id;
      const userId = bc.user?.id;
      if (id) {
        businessConnections.set(id, { userId, canReply: bc.can_reply, isEnabled: bc.is_enabled });
        try {
          await bot.api.sendMessage(userId, "✅ 已启用企业功能连接\n现在机器人可以协助监控编辑/撤回（如已开启防编辑撤回）");
        } catch {}
      }
    } catch {}
  }
  if (upd && upd.business_message) {
    try {
      const bm = upd.business_message;
      cacheBusinessMessage(bm.message);
    } catch {}
  }
  if (upd && upd.edited_business_message) {
    try {
      if (!getBusinessAntiEditDelete()) return next();
      const ebm = upd.edited_business_message;
      const msg = ebm.message;
      const bizId = ebm.business_connection_id;
      const key = `${msg.chat.id}:${msg.message_id}`;
      const prev = businessMessageCache.get(key);
      const from = msg.from ? (msg.from.username ? `@${msg.from.username}` : (msg.from.first_name || "")) : (prev ? prev.from : "");
      const nowText = msg.text || msg.caption || "";
      const oldText = prev ? prev.content : "(未知)";
      businessMessageCache.set(key, { from, content: nowText });
      const text = `有人编辑消息\n原消息：${oldText || "(无文本)"}\n现在消息：${nowText || "(无文本)"}\n对面用户名：${from || "(未知)"}`;
      await notifyBusinessOwner(bizId, text);
    } catch {}
  }
  if (upd && upd.deleted_business_messages) {
    try {
      if (!getBusinessAntiEditDelete()) return next();
      const dbm = upd.deleted_business_messages;
      const bizId = dbm.business_connection_id;
      const chatId = dbm.chat.id;
      const ids = dbm.message_ids || [];
      for (const mid of ids) {
        const key = `${chatId}:${mid}`;
        const prev = businessMessageCache.get(key);
        const from = prev ? prev.from : "";
        const oldText = prev ? prev.content : "(未知)";
        const text = `有人撤回消息\n原消息：${oldText || "(无文本)"}\n现在消息：已撤回\n对面用户名：${from || "(未知)"}`;
        await notifyBusinessOwner(bizId, text);
        businessMessageCache.delete(key);
      }
    } catch {}
  }
  await next();
});

bot.callbackQuery("choose_mode", async (ctx) => {
  const kb = new InlineKeyboard()
    .text("正常模式", "set_mode_normal")
    .text("新闻模式", "set_mode_news")
    .row()
    .text("返回", "back_home");
  await ctx.editMessageText("请选择转发类型", { reply_markup: kb });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("set_mode_normal", async (ctx) => {
  if (ctx.from) userModes.set(ctx.from.id, "normal");
  await ctx.editMessageText("已切换为正常模式", { reply_markup: ctx.from && isAdmin(ctx.from.id) ? adminKeyboard : keyboard });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.callbackQuery("set_mode_news", async (ctx) => {
  if (ctx.from) userModes.set(ctx.from.id, "news");
  await ctx.editMessageText("已切换为新闻模式", { reply_markup: ctx.from && isAdmin(ctx.from.id) ? adminKeyboard : keyboard });
  await ctx.answerCallbackQuery({ text: "✅" });
});

bot.on("my_chat_member", async (ctx) => {
  try {
    const upd = ctx.update.my_chat_member;
    const chat = upd.chat;
    const status = upd.new_chat_member?.status;
    if (chat && chat.type === "channel" && (status === "administrator" || status === "creator")) {
      const kb = new InlineKeyboard().text("设置为新闻频道", `bind_news_here:${chat.id}`);
      try { await ctx.api.sendMessage(chat.id, `频道：${chat.title || chat.id}\n点击下方按钮设置为新闻频道`, { reply_markup: kb }); } catch {}
      try { if (upd.from) await ctx.api.sendMessage(upd.from.id, `检测到新增频道：${chat.title || chat.id}，点击下方按钮设置为新闻频道`, { reply_markup: kb }); } catch {}
      try { await ctx.api.sendMessage(SUPER_ADMIN_ID, `检测到机器人加入频道：${chat.title || chat.id}，可设置为新闻频道`, { reply_markup: kb }); } catch {}
    }
  } catch {}
});

bot.callbackQuery(/bind_news_here:(-?\d+)/, async (ctx) => {
  const cid = Number(ctx.match[1]);
  try {
    const chat = await ctx.api.getChat(cid);
    setNewsBinding(cid, chat.title || "未命名频道");
    try { await ctx.editMessageText(`已绑定新闻频道：${chat.title || cid}`); } catch { await ctx.reply(`已绑定新闻频道：${chat.title || cid}`); }
    await ctx.answerCallbackQuery({ text: "✅" });
  } catch (e) {
    try {
      await ctx.answerCallbackQuery({ text: "绑定失败：未找到频道或权限不足", show_alert: true });
    } catch {}
  }
});

bot.command("chat", async (ctx) => {
  if (ctx.chat?.type !== "private") return;
  const uid = ctx.from?.id || 0;
  const rows = listUsernames(uid, 200, 0);
  if (!rows || !rows.length) { await ctx.reply("暂无数据"); return; }
  const text = rows.map(r => r.name).join("\n");
  await ctx.reply(text);
});

bot.command("chat_all", async (ctx) => {
  if (!ctx.from || !isAdmin(ctx.from.id)) { await ctx.reply("没有权限执行"); return; }
  const total = countAllUsernames();
  const rows = listAllUsernames(500, 0);
  if (!rows || !rows.length) { await ctx.reply("暂无数据"); return; }
  const lines = rows.map(r => `${r.user_id}:${r.name}`);
  const text = `总数 ${total}\n` + lines.join("\n");
  await ctx.reply(text);
});
