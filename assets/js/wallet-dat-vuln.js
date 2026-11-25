/* wallet-dat-vuln.js — Wallet.dat Vulnerability Scanner (100% client-side)
 *
 * Upload a Bitcoin Core wallet.dat; this engine byte-scans it for private-key
 * records, classifies every weakness, dumps recoverable keys, and — for
 * encrypted wallets — extracts the hashcat mode-11300 "$bitcoin$" hash for
 * OFFLINE cracking (no passphrase brute-forcing happens in the browser).
 *
 * Reuses the crypto the site already loads on crypto pages:
 *   window.NobleHashes  (sha256 / sha512 / ripemd160)
 *   window.NobleCurves  (secp256k1.getPublicKey)
 *   window.crypto.subtle (AES-256-CBC)
 * base58check + bech32 + WIF are bundled here (small, self-contained).
 *
 * The file never leaves the browser: only FileReader / fetch of local samples.
 */
(function (global) {
  'use strict';

  // ---- lazy crypto deps (so Node tests can inject shims) -------------------
  function NH() { return global.NobleHashes || {}; }
  function NC() { return global.NobleCurves || {}; }
  function subtle() { return (global.crypto || (typeof crypto !== 'undefined' ? crypto : null)).subtle; }
  function sha256(b) { return NH().sha256Module.sha256(b); }
  function sha512(b) { return NH().sha512Module.sha512(b); }
  function ripemd160(b) { return NH().ripemd160Module.ripemd160(b); }
  function hash256(b) { return sha256(sha256(b)); }
  function hash160(b) { return ripemd160(sha256(b)); }
  function getPub(secret, compressed) {
    return NC().secp256k1Module.secp256k1.getPublicKey(secret, compressed);
  }

  // ---- byte utils ----------------------------------------------------------
  function hex(b) { let s = ''; for (let i = 0; i < b.length; i++) s += b[i].toString(16).padStart(2, '0'); return s; }
  function hexToBytes(h) { const a = new Uint8Array(h.length / 2); for (let i = 0; i < a.length; i++) a[i] = parseInt(h.substr(i * 2, 2), 16); return a; }
  function concat() { let n = 0; for (const a of arguments) n += a.length; const out = new Uint8Array(n); let o = 0; for (const a of arguments) { out.set(a, o); o += a.length; } return out; }
  function u32le(b, i) { return (b[i] | (b[i + 1] << 8) | (b[i + 2] << 16) | (b[i + 3] << 24)) >>> 0; }
  function eqAt(b, i, pat) { if (i + pat.length > b.length) return false; for (let k = 0; k < pat.length; k++) if (b[i + k] !== pat[k]) return false; return true; }

  // ---- base58 / base58check ------------------------------------------------
  var B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
  function base58encode(bytes) {
    let zeros = 0; while (zeros < bytes.length && bytes[zeros] === 0) zeros++;
    let num = 0n; for (let i = 0; i < bytes.length; i++) num = (num << 8n) + BigInt(bytes[i]);
    let out = ''; while (num > 0n) { out = B58[Number(num % 58n)] + out; num /= 58n; }
    return '1'.repeat(zeros) + out;
  }
  function base58check(payload) { return base58encode(concat(payload, hash256(payload).slice(0, 4))); }

  // ---- bech32 (BIP173, segwit v0) ------------------------------------------
  var B32 = 'qpzry9x8gf2tvdw0s3jn54khce6mua7l';
  function b32Polymod(v) { let chk = 1; var G = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]; for (const x of v) { const b = chk >>> 25; chk = ((chk & 0x1ffffff) << 5) ^ x; for (let i = 0; i < 5; i++) if ((b >> i) & 1) chk ^= G[i]; } return chk >>> 0; }
  function b32Hrp(h) { const r = []; for (let i = 0; i < h.length; i++) r.push(h.charCodeAt(i) >> 5); r.push(0); for (let i = 0; i < h.length; i++) r.push(h.charCodeAt(i) & 31); return r; }
  function b32Checksum(h, d) { const v = b32Hrp(h).concat(d).concat([0, 0, 0, 0, 0, 0]); const m = b32Polymod(v) ^ 1; const r = []; for (let i = 0; i < 6; i++) r.push((m >> (5 * (5 - i))) & 31); return r; }
  function convertBits(data, from, to, pad) { let acc = 0, bits = 0; const ret = []; const max = (1 << to) - 1; for (const val of data) { acc = ((acc << from) | val) >>> 0; bits += from; while (bits >= to) { bits -= to; ret.push((acc >> bits) & max); } } if (pad && bits) ret.push((acc << (to - bits)) & max); return ret; }
  function bech32Encode(hrp, data) { const c = data.concat(b32Checksum(hrp, data)); let s = hrp + '1'; for (const d of c) s += B32.charAt(d); return s; }
  function p2wpkh(h160, hrp) { return bech32Encode(hrp, [0].concat(convertBits(Array.from(h160), 8, 5, true))); }

  // ---- addresses / WIF -----------------------------------------------------
  var NETS = {
    'bitcoin':      { name: 'Bitcoin',      wif: 0x80, p2pkh: 0x00, p2sh: 0x05, hrp: 'bc' },
    'litecoin':     { name: 'Litecoin',     wif: 0xb0, p2pkh: 0x30, p2sh: 0x32, hrp: 'ltc' },
    'dogecoin':     { name: 'Dogecoin',     wif: 0x9e, p2pkh: 0x1e, p2sh: 0x16, hrp: null },
    'bitcoin-cash': { name: 'Bitcoin Cash', wif: 0x80, p2pkh: 0x00, p2sh: 0x05, hrp: null }
  };
  function p2pkh(h160, ver) { return base58check(concat(Uint8Array.of(ver), h160)); }
  function p2shP2wpkh(h160, ver) { const redeem = concat(Uint8Array.of(0x00, 0x14), h160); return base58check(concat(Uint8Array.of(ver), hash160(redeem))); }
  function toWIF(secret32, compressed, ver) { let p = concat(Uint8Array.of(ver), secret32); if (compressed) p = concat(p, Uint8Array.of(0x01)); return base58check(p); }
  function deriveFromSecret(secret32, net) {
    net = net || NETS.bitcoin;
    const pubC = getPub(secret32, true);
    const h = hash160(pubC);
    return {
      secretHex: hex(secret32),
      pubkey: hex(pubC),
      wif: toWIF(secret32, true, net.wif),
      wifUncompressed: toWIF(secret32, false, net.wif),
      p2pkh: p2pkh(h, net.p2pkh),
      p2wpkh: net.hrp ? p2wpkh(h, net.hrp) : null,
      p2sh: p2shP2wpkh(h, net.p2sh)
    };
  }

  // ---- format detect -------------------------------------------------------
  function detectFormat(b) {
    if (b.length >= 16 && eqAt(b, 0, [0x53, 0x51, 0x4c, 0x69, 0x74, 0x65, 0x20, 0x66, 0x6f, 0x72, 0x6d, 0x61, 0x74, 0x20, 0x33, 0x00])) return 'sqlite';
    // Berkeley DB magic 0x00061561 (btree) at offset 12, either byte order
    if (b.length >= 16) {
      var m1 = u32le(b, 12);
      if (m1 === 0x00061561 || m1 === 0x61150600) return 'bdb';
    }
    return 'unknown';
  }

  // ---- raw-scan record extraction -----------------------------------------
  // Two CPrivKey DER encodings; the 32-byte secret follows the 04 20 octet-string tag.
  var DER1 = [0x30, 0x81, 0xd3, 0x02, 0x01, 0x01, 0x04, 0x20];        // 214-byte form
  var DER2 = [0x30, 0x82, 0x01, 0x13, 0x02, 0x01, 0x01, 0x04, 0x20];  // 279-byte form
  function findPlaintextKeys(b) {
    var out = [], seen = {};
    for (var i = 0; i + 40 < b.length; i++) {
      var pre = eqAt(b, i, DER1) ? DER1.length : (eqAt(b, i, DER2) ? DER2.length : 0);
      if (!pre) continue;
      var sec = b.slice(i + pre, i + pre + 32);
      if (sec.length !== 32) continue;
      var allZero = true; for (var k = 0; k < 32; k++) if (sec[k]) { allZero = false; break; }
      if (allZero) continue;
      var hh = hex(sec);
      if (seen[hh]) continue; seen[hh] = 1;
      out.push({ offset: i, secretHex: hh });
    }
    return out;
  }
  // mkey value: 0x30 <48 enc-master> 0x08 <8 salt> <u32 method=0> <u32 iters> [0x00]
  function findMkeys(b) {
    var out = [], seen = {};
    for (var i = 0; i + 66 <= b.length; i++) {
      if (b[i] !== 0x30 || b[i + 49] !== 0x08) continue;
      var method = u32le(b, i + 58);
      if (method !== 0) continue;
      var iters = u32le(b, i + 62);
      if (iters < 1 || iters > 100000000) continue;
      if (i + 66 < b.length && b[i + 66] !== 0x00) continue; // empty vchOtherDerivationParameters
      var enc = hex(b.slice(i + 1, i + 49));
      var salt = hex(b.slice(i + 50, i + 58));
      var key = enc + salt + iters;
      if (seen[key]) continue; seen[key] = 1;
      out.push({ offset: i, encMasterHex: enc, saltHex: salt, iterations: iters });
    }
    return out;
  }
  // ckey record: 04 "ckey" 21 <33 pubkey> ... then nearby 0x30 <48 enc>
  var CKEY = [0x04, 0x63, 0x6b, 0x65, 0x79, 0x21];
  function findCkeys(b) {
    var out = [], seen = {};
    for (var i = 0; i + 6 + 33 < b.length; i++) {
      if (!eqAt(b, i, CKEY)) continue;
      var pub = b.slice(i + 6, i + 6 + 33);
      if (pub[0] !== 0x02 && pub[0] !== 0x03) continue; // compressed pubkey prefix
      var pubHex = hex(pub);
      // find the 48-byte encrypted blob (0x30 + 48 bytes) shortly after the key
      var enc = null;
      for (var j = i + 6 + 33; j < Math.min(b.length - 49, i + 6 + 33 + 96); j++) {
        if (b[j] === 0x30 && j + 49 <= b.length) { enc = hex(b.slice(j + 1, j + 49)); break; }
      }
      if (seen[pubHex]) continue; seen[pubHex] = 1;
      out.push({ offset: i, pubkeyHex: pubHex, encHex: enc });
    }
    return out;
  }
  function findMarkers(b) {
    function has(str) { var p = []; for (var i = 0; i < str.length; i++) p.push(str.charCodeAt(i)); for (var j = 0; j + p.length <= b.length; j++) if (eqAt(b, j, p)) return true; return false; }
    return { hdchain: has('hdchain'), hdseed: has('hdseed'), defaultkey: has('defaultkey'), name: has('\x04name') };
  }

  // ---- hashcat mode-11300 "$bitcoin$" hash ---------------------------------
  function buildBitcoinHash(mkey, ckey) {
    var cm = mkey.encMasterHex, salt = mkey.saltHex, rounds = mkey.iterations, h;
    if (ckey && ckey.encHex && ckey.pubkeyHex) {
      h = '$bitcoin$' + cm.length + '$' + cm + '$' + salt.length + '$' + salt + '$' + rounds +
          '$' + ckey.encHex.length + '$' + ckey.encHex + '$' + ckey.pubkeyHex.length + '$' + ckey.pubkeyHex;
    } else {
      h = '$bitcoin$' + cm.length + '$' + cm + '$' + salt.length + '$' + salt + '$' + rounds + '$2$00$2$00';
    }
    return { hash: h, hashcat: 'hashcat -m 11300 -a 0 wallet.hash wordlist.txt', john: 'john --format=bitcoin wallet.hash' };
  }

  // ---- optional passphrase decrypt (NOT brute force) -----------------------
  function evpKdfSha512(passBytes, saltBytes, iters) {
    var d = sha512(concat(passBytes, saltBytes));
    for (var i = 1; i < iters; i++) d = sha512(d);
    return { key32: d.slice(0, 32), iv16: d.slice(32, 48) };
  }
  async function aesCbcDecrypt(key, iv, ct) {
    var k = await subtle().importKey('raw', key, { name: 'AES-CBC' }, false, ['decrypt']);
    var pt = await subtle().decrypt({ name: 'AES-CBC', iv: iv }, k, ct);
    return new Uint8Array(pt);
  }
  async function decryptWallet(passphrase, mkey, ckeys) {
    var enc = new TextEncoder().encode(passphrase);
    var kdf = evpKdfSha512(enc, hexToBytes(mkey.saltHex), mkey.iterations);
    var master = await aesCbcDecrypt(kdf.key32, kdf.iv16, hexToBytes(mkey.encMasterHex)); // throws => wrong passphrase
    var out = [];
    for (var i = 0; i < ckeys.length; i++) {
      var ck = ckeys[i]; if (!ck.encHex) continue;
      var pub = hexToBytes(ck.pubkeyHex);
      var iv = hash256(pub).slice(0, 16);
      try {
        var secret = await aesCbcDecrypt(master, iv, hexToBytes(ck.encHex));
        var ok = hex(getPub(secret, pub.length === 33)) === ck.pubkeyHex;
        out.push({ pubkeyHex: ck.pubkeyHex, secretHex: hex(secret), ok: ok });
      } catch (e) { out.push({ pubkeyHex: ck.pubkeyHex, ok: false }); }
    }
    return { masterOk: true, keys: out };
  }

  // ---- top-level analysis --------------------------------------------------
  async function analyze(buf, opts) {
    opts = opts || {};
    var net = NETS[opts.net || 'bitcoin'] || NETS.bitcoin;
    var b = (buf instanceof Uint8Array) ? buf : new Uint8Array(buf);
    var format = detectFormat(b);
    var plain = findPlaintextKeys(b);
    var mkeys = findMkeys(b);
    var ckeys = findCkeys(b);
    var markers = findMarkers(b);
    var encrypted = mkeys.length > 0;
    var vulns = [], keys = [];

    for (var i = 0; i < plain.length; i++) {
      var d = null; try { d = deriveFromSecret(hexToBytes(plain[i].secretHex), net); } catch (e) { }
      keys.push(Object.assign({ source: encrypted ? 'slack/deleted' : 'plaintext', offset: plain[i].offset, secretHex: plain[i].secretHex }, d || {}));
    }

    if (plain.length && !encrypted)
      vulns.push({ id: 'V1', severity: 'critical', title: 'Unencrypted wallet — plaintext private keys', detail: 'The wallet is NOT encrypted: ' + plain.length + ' private key(s) are stored in plaintext and are dumped below. Anyone with this file has full spending control.' });
    if (plain.length && encrypted)
      vulns.push({ id: 'V4', severity: 'high', title: 'Slack-space / deleted plaintext keys recovered', detail: plain.length + ' plaintext key(s) were found by raw byte-scan even though the wallet is encrypted — typically leftover keys from before the wallet was encrypted or from deleted addresses. They are recoverable without the passphrase and are dumped below.' });

    var bitcoinHash = null;
    if (encrypted) {
      bitcoinHash = buildBitcoinHash(mkeys[0], ckeys[0]);
      vulns.push({ id: 'V2', severity: 'high', title: 'Encrypted — offline-crackable KDF hash extracted', detail: 'The wallet is AES-256-CBC encrypted. Its master-key hash was extracted in hashcat mode-11300 format for OFFLINE passphrase cracking. Strength depends entirely on the passphrase.', hash: bitcoinHash.hash, hashcat: bitcoinHash.hashcat, john: bitcoinHash.john });
      var it = mkeys[0].iterations;
      if (it < 100000)
        vulns.push({ id: 'V3', severity: it <= 25000 ? 'high' : 'medium', title: 'Weak KDF iteration count (' + it + ')', detail: 'The passphrase KDF uses only ' + it + ' SHA-512 rounds (modern Bitcoin Core targets far more). Low iteration counts make offline cracking dramatically faster.' });
    }

    if (markers.hdchain || markers.hdseed)
      vulns.push({ id: 'V5', severity: encrypted ? 'info' : 'high', title: 'HD wallet seed present (single point of failure)', detail: 'An HD chain/seed record is present. One seed derives every key in the wallet — if it is unencrypted or the passphrase is cracked, all derived keys fall at once.' });

    if (encrypted && opts.passphrase) {
      try {
        var res = await decryptWallet(opts.passphrase, mkeys[0], ckeys);
        var good = res.keys.filter(function (r) { return r.ok; });
        for (var g = 0; g < good.length; g++) {
          var dd = null; try { dd = deriveFromSecret(hexToBytes(good[g].secretHex), net); } catch (e) { }
          keys.push(Object.assign({ source: 'decrypted', secretHex: good[g].secretHex }, dd || {}));
        }
        vulns.push({ id: 'V6', severity: 'critical', title: 'Passphrase correct — keys decrypted', detail: 'The supplied passphrase decrypted the master key' + (good.length ? ' and ' + good.length + ' private key(s), dumped below.' : ' (no ckey records paired to decrypt).') });
      } catch (e) {
        vulns.push({ id: 'V6', severity: 'info', title: 'Passphrase incorrect', detail: 'The supplied passphrase did not decrypt the master key (padding check failed). Use the extracted $bitcoin$ hash with hashcat/John instead.' });
      }
    }

    return {
      format: format,
      encrypted: encrypted,
      network: net.name,
      counts: { plaintext: plain.length, ckey: ckeys.length, mkey: mkeys.length },
      vulns: vulns,
      keys: keys,
      bitcoinHash: bitcoinHash,
      markers: markers
    };
  }

  // ---- browser UI glue -----------------------------------------------------
  var state = { file: null, buf: null, net: 'bitcoin', report: null };
  function $(id) { return (typeof document !== 'undefined') ? document.getElementById(id) : null; }
  function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;'); }
  function fmtSize(n) { return n < 1024 ? n + ' B' : n < 1048576 ? (n / 1024).toFixed(1) + ' KB' : (n / 1048576).toFixed(2) + ' MB'; }
  var SEV = { critical: '#e74c3c', high: '#e67e22', medium: '#f1c40f', info: '#3498db' };

  function setFile(file, buf) {
    state.file = file; state.buf = buf;
    var sel = $('wdvSelected'), up = $('wdvUploadPrompt');
    if (sel && up) { sel.classList.remove('d-none'); up.classList.add('d-none'); }
    if ($('wdvFileName')) $('wdvFileName').textContent = file.name;
    if ($('wdvFileSize')) $('wdvFileSize').textContent = fmtSize(file.size);
    if ($('wdvScanBtn')) $('wdvScanBtn').disabled = false;
  }
  function readFile(file) {
    return new Promise(function (resolve, reject) {
      var r = new FileReader();
      r.onload = function () { resolve(new Uint8Array(r.result)); };
      r.onerror = function () { reject(r.error); };
      r.readAsArrayBuffer(file);
    });
  }

  var WalletDatVuln = {
    init: function () {
      if (typeof document === 'undefined') return;
      var input = $('wdvFile'), area = $('wdvUploadArea');
      if (input) input.addEventListener('change', function (e) { if (e.target.files[0]) WalletDatVuln.handleFile(e.target.files[0]); });
      if (area) {
        area.addEventListener('dragover', function (e) { e.preventDefault(); area.classList.add('wdv-drag'); });
        area.addEventListener('dragleave', function () { area.classList.remove('wdv-drag'); });
        area.addEventListener('drop', function (e) { e.preventDefault(); area.classList.remove('wdv-drag'); if (e.dataTransfer.files[0]) WalletDatVuln.handleFile(e.dataTransfer.files[0]); });
      }
    },
    handleFile: async function (file) {
      try { var buf = await readFile(file); setFile(file, buf); }
      catch (e) { alert('Could not read file: ' + e); }
    },
    clearFile: function () {
      state.file = null; state.buf = null;
      if ($('wdvSelected')) $('wdvSelected').classList.add('d-none');
      if ($('wdvUploadPrompt')) $('wdvUploadPrompt').classList.remove('d-none');
      if ($('wdvScanBtn')) $('wdvScanBtn').disabled = true;
      if ($('wdvResults')) $('wdvResults').classList.add('d-none');
      if ($('wdvFile')) $('wdvFile').value = '';
    },
    togglePassword: function () { var p = $('wdvPass'); if (p) p.type = p.type === 'password' ? 'text' : 'password'; },
    selectChain: function (chain) {
      state.net = chain;
      var btns = document.querySelectorAll('.wdv-chain-btn');
      for (var i = 0; i < btns.length; i++) btns[i].classList.toggle('active', btns[i].getAttribute('data-chain') === chain);
    },
    loadSample: async function (name) {
      try {
        var resp = await fetch('./assets/dat/' + name);
        if (!resp.ok) throw new Error('HTTP ' + resp.status);
        var buf = new Uint8Array(await resp.arrayBuffer());
        setFile({ name: name, size: buf.length }, buf);
        WalletDatVuln.scan();
      } catch (e) { alert('Could not load sample "' + name + '": ' + e); }
    },
    scan: async function () {
      if (!state.buf) { alert('Select a wallet.dat file first.'); return; }
      var prog = $('wdvProgress'), res = $('wdvResults');
      if (prog) prog.classList.remove('d-none');
      if (res) res.classList.add('d-none');
      await new Promise(function (r) { setTimeout(r, 20); });
      try {
        var pass = $('wdvPass') ? $('wdvPass').value.trim() : '';
        var report = await analyze(state.buf, { net: state.net, passphrase: pass || undefined });
        state.report = report;
        WalletDatVuln.render(report);
      } catch (e) {
        alert('Scan failed: ' + (e && e.message ? e.message : e));
      } finally {
        if (prog) prog.classList.add('d-none');
      }
    },
    render: function (r) {
      var res = $('wdvResults'); if (!res) return;
      if ($('wdvFormat')) $('wdvFormat').textContent = r.format === 'bdb' ? 'Berkeley DB' : r.format === 'sqlite' ? 'SQLite (descriptor)' : 'Unknown';
      if ($('wdvEncrypted')) $('wdvEncrypted').textContent = r.encrypted ? 'Yes (AES-256-CBC)' : 'No';
      if ($('wdvKeyCount')) $('wdvKeyCount').textContent = r.keys.length;
      if ($('wdvVulnCount')) $('wdvVulnCount').textContent = r.vulns.length;

      // vulnerabilities
      var vl = $('wdvVulnList');
      if (vl) {
        if (!r.vulns.length) {
          vl.innerHTML = '<div class="alert alert-success mb-0">No vulnerabilities detected by the byte-scan. If this is an encrypted wallet with no leftover plaintext keys, that is expected.</div>';
        } else {
          var html = '';
          for (var i = 0; i < r.vulns.length; i++) {
            var v = r.vulns[i]; var c = SEV[v.severity] || '#888';
            html += '<div class="wdv-vuln" style="border-left:4px solid ' + c + '">' +
              '<div class="wdv-vuln-head"><span class="wdv-badge" style="background:' + c + '">' + esc(v.severity.toUpperCase()) + '</span>' +
              '<strong>' + esc(v.title) + '</strong></div>' +
              '<div class="wdv-vuln-body">' + esc(v.detail) + '</div>';
            if (v.hash) {
              html += '<div class="wdv-hash-box"><label>hashcat mode-11300 hash</label>' +
                '<textarea class="form-control wdv-hash" readonly rows="2">' + esc(v.hash) + '</textarea>' +
                '<div class="wdv-hash-cmds"><code>' + esc(v.hashcat) + '</code><br><code>' + esc(v.john) + '</code></div>' +
                '<button class="btn btn-sm btn-outline-secondary mt-2" onclick="WalletDatVuln.copyHash()">Copy hash</button></div>';
            }
            html += '</div>';
          }
          vl.innerHTML = html;
        }
      }

      // keys table
      var kb = $('wdvKeysBody');
      if (kb) {
        if (!r.keys.length) {
          kb.innerHTML = '<tr><td colspan="4" class="text-muted text-center">No private keys recoverable without the passphrase.</td></tr>';
        } else {
          var rows = '';
          for (var j = 0; j < r.keys.length; j++) {
            var k = r.keys[j];
            var addr = k.p2pkh || '-';
            rows += '<tr><td class="wdv-mono">' + esc(k.secretHex) + '</td>' +
              '<td class="wdv-mono">' + esc(k.wif || '-') + '</td>' +
              '<td class="wdv-mono">' + esc(addr) + '</td>' +
              '<td><span class="badge bg-secondary">' + esc(k.source) + '</span></td></tr>';
          }
          kb.innerHTML = rows;
        }
      }
      res.classList.remove('d-none');
    },
    copyHash: function () {
      var h = state.report && state.report.bitcoinHash ? state.report.bitcoinHash.hash : '';
      if (h && navigator.clipboard) navigator.clipboard.writeText(h);
    },
    exportReport: function () {
      if (!state.report) return;
      var blob = new Blob([JSON.stringify(state.report, null, 2)], { type: 'application/json' });
      var a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = (state.file && state.file.name ? state.file.name : 'wallet') + '.vuln-report.json';
      a.click();
    }
  };

  global.WalletDatVuln = WalletDatVuln;
  if (typeof document !== 'undefined') {
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', WalletDatVuln.init);
    else WalletDatVuln.init();
  }

  // ---- Node test export ----------------------------------------------------
  if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
      detectFormat: detectFormat, findPlaintextKeys: findPlaintextKeys, findMkeys: findMkeys,
      findCkeys: findCkeys, findMarkers: findMarkers, buildBitcoinHash: buildBitcoinHash,
      evpKdfSha512: evpKdfSha512, aesCbcDecrypt: aesCbcDecrypt, decryptWallet: decryptWallet,
      deriveFromSecret: deriveFromSecret, base58check: base58check, p2pkh: p2pkh, p2wpkh: p2wpkh,
      toWIF: toWIF, hash160: hash160, hash256: hash256, hex: hex, hexToBytes: hexToBytes,
      analyze: analyze, NETS: NETS
    };
  }
})(typeof window !== 'undefined' ? window : globalThis);
