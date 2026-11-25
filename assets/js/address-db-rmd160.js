/*!
 * address-db-rmd160.js — ADDRESS-DATABASE engine: RMD160 (HASH160) -> chain address -> balance.
 *
 * Model (identical for every chain)
 * ---------------------------------
 * Column 1 = the 40-hex RMD160 (HASH160) index — the 160-bit value V.
 * Column 2 = the chain-native address rendered from those same 20 bytes.
 * Column 3 = the balance, via BalanceChecker.fetchXxxBalancesBatch().
 *
 * There is NO private key anywhere on these pages. A 20-byte value cannot be a
 * private key, and for every chain whose address payload is exactly 20 bytes
 * (EVM 0x…, Tron T…, XRP r…, Litecoin L…, Dogecoin D…, Zcash t1…, BCH 1…) the
 * rendered address is the honest, real encoding of that value. For chains whose
 * native key width is 32 (Solana / TON / Sui) or 64 bytes (Monero) the 20 bytes
 * are expanded deterministically to the native width so the rendered address is
 * always a well-formed native address — never a truncated or bogus one.
 *
 * Everything is self-contained (Keccak-256, Base58, Base58Check, bech32, CRC16,
 * Monero block-Base58) except SHA-256, which uses the platform WebCrypto.
 */
(function (root) {
  'use strict';

  var MASK64 = (1n << 64n) - 1n;

  // ------------------------------------------------------------------ Keccak-256
  // Original Keccak (0x01 padding) — used by Ethereum (EIP-55) and Monero.
  var RC = [
    0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n,
    0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n,
    0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an,
    0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n,
    0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an,
    0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n
  ];
  var RHO = [
    0, 1, 62, 28, 27,
    36, 44, 6, 55, 20,
    3, 10, 43, 25, 39,
    41, 45, 15, 21, 8,
    18, 2, 61, 56, 14
  ];
  function rotl(v, n) {
    n = BigInt(n);
    if (n === 0n) return v & MASK64;
    return ((v << n) | (v >> (64n - n))) & MASK64;
  }
  function keccakF(A) {
    var x, y, round, C, D, B;
    for (round = 0; round < 24; round++) {
      // theta
      C = new Array(5); D = new Array(5);
      for (x = 0; x < 5; x++) C[x] = A[x] ^ A[x + 5] ^ A[x + 10] ^ A[x + 15] ^ A[x + 20];
      for (x = 0; x < 5; x++) D[x] = C[(x + 4) % 5] ^ rotl(C[(x + 1) % 5], 1);
      for (x = 0; x < 5; x++) for (y = 0; y < 5; y++) A[x + 5 * y] = (A[x + 5 * y] ^ D[x]) & MASK64;
      // rho + pi
      B = new Array(25);
      for (x = 0; x < 5; x++) for (y = 0; y < 5; y++) {
        B[y + 5 * ((2 * x + 3 * y) % 5)] = rotl(A[x + 5 * y], RHO[x + 5 * y]);
      }
      // chi
      for (x = 0; x < 5; x++) for (y = 0; y < 5; y++) {
        A[x + 5 * y] = (B[x + 5 * y] ^ ((~B[((x + 1) % 5) + 5 * y] & MASK64) & B[((x + 2) % 5) + 5 * y])) & MASK64;
      }
      // iota
      A[0] = (A[0] ^ RC[round]) & MASK64;
    }
    return A;
  }
  function keccak256(bytes) {
    var rate = 136, msg = Array.prototype.slice.call(bytes), i, b, off, lane;
    var padLen = rate - (msg.length % rate);
    if (padLen === 1) {
      msg.push(0x81);
    } else {
      msg.push(0x01);
      while (msg.length % rate !== 0) msg.push(0x00);
      msg[msg.length - 1] |= 0x80;
    }
    var A = new Array(25);
    for (i = 0; i < 25; i++) A[i] = 0n;
    for (off = 0; off < msg.length; off += rate) {
      for (i = 0; i < rate / 8; i++) {
        lane = 0n;
        for (b = 0; b < 8; b++) lane |= BigInt(msg[off + i * 8 + b]) << BigInt(8 * b);
        A[i] = (A[i] ^ lane) & MASK64;
      }
      keccakF(A);
    }
    var out = [];
    for (i = 0; i < 4; i++) {
      lane = A[i];
      for (b = 0; b < 8; b++) out.push(Number((lane >> BigInt(8 * b)) & 0xffn));
    }
    return out;
  }

  // ------------------------------------------------------------------ SHA-256
  function sha256(bytes) {
    var flat = (typeof bytes === 'string') ? strToBytes(bytes) : Array.prototype.slice.call(bytes);
    var u8 = new Uint8Array(flat);
    var subtle = (root.crypto && root.crypto.subtle) ? root.crypto.subtle : null;
    if (!subtle) return Promise.reject(new Error('WebCrypto unavailable'));
    return subtle.digest('SHA-256', u8).then(function (h) { return Array.prototype.slice.call(new Uint8Array(h)); });
  }
  function strToBytes(s) { var o = [], i; for (i = 0; i < s.length; i++) o.push(s.charCodeAt(i) & 0xff); return o; }
  function bytesToStr(b) { return String.fromCharCode.apply(null, b); }
  function hexToBytes(hex) { var o = [], i; for (i = 0; i < hex.length; i += 2) o.push(parseInt(hex.substr(i, 2), 16)); return o; }
  function bytesToHex(b) { var o = '', i; for (i = 0; i < b.length; i++) o += b[i].toString(16).padStart(2, '0'); return o; }

  // ------------------------------------------------------------------ Base58
  var B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
  var RIPPLE_B58 = 'rpshnaf39wBUDNEGHJKLM4PQRST7VWXYZ2bcdeCg65jkm8oFqi1tuvAxyz';

  function b58encode(bytes, alphabet) {
    alphabet = alphabet || B58;
    var digits = [0], i, j;
    for (i = 0; i < bytes.length; i++) {
      var carry = bytes[i];
      for (j = 0; j < digits.length; j++) { carry += digits[j] << 8; digits[j] = carry % 58; carry = (carry / 58) | 0; }
      while (carry) { digits.push(carry % 58); carry = (carry / 58) | 0; }
    }
    var str = '';
    for (i = 0; i < bytes.length && bytes[i] === 0; i++) str += alphabet.charAt(0);
    for (j = digits.length - 1; j >= 0; j--) str += alphabet.charAt(digits[j]);
    return str;
  }

  // Base58Check with an arbitrary-length version prefix and double-SHA-256 checksum.
  function b58check(version, payload) {
    var body = version.concat(payload);
    return sha256(body).then(function (h1) {
      return sha256(h1).then(function (h2) {
        return b58encode(body.concat(h2.slice(0, 4)));
      });
    });
  }

  // Monero block-based Base58 (8-byte blocks -> 11 chars).
  function moneroB58(bytes) {
    var out = '', i, j;
    for (i = 0; i < bytes.length; i += 8) {
      var block = bytes.slice(i, i + 8);
      var num = 0n;
      for (j = 0; j < block.length; j++) num = (num << 8n) | BigInt(block[j]);
      var size = Math.ceil(block.length * 8 / 6);
      var enc = '';
      while (num > 0n) { enc = B58.charAt(Number(num % 58n)) + enc; num = num / 58n; }
      while (enc.length < size) enc = B58.charAt(0) + enc;
      out += enc;
    }
    return out;
  }

  // ------------------------------------------------------------------ bech32 (BIP173)
  var BECH32 = 'qpzry9x8gf2tvdw0s3jn54khce6mua7l';
  function bech32Polymod(values) {
    var GEN = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3], chk = 1, i, p;
    for (p = 0; p < values.length; p++) {
      var top = chk >>> 25;
      chk = ((chk & 0x1ffffff) << 5) ^ values[p];
      for (i = 0; i < 5; i++) if ((top >>> i) & 1) chk ^= GEN[i];
    }
    return chk >>> 0;
  }
  function bech32HrpExpand(hrp) {
    var ret = [], i;
    for (i = 0; i < hrp.length; i++) ret.push(hrp.charCodeAt(i) >>> 5);
    ret.push(0);
    for (i = 0; i < hrp.length; i++) ret.push(hrp.charCodeAt(i) & 31);
    return ret;
  }
  function bech32Checksum(hrp, data, spec) {
    var values = bech32HrpExpand(hrp).concat(data).concat([0, 0, 0, 0, 0, 0]);
    var mod = bech32Polymod(values) ^ spec, ret = [], p;
    for (p = 0; p < 6; p++) ret.push((mod >>> (5 * (5 - p))) & 31);
    return ret;
  }
  function bech32Encode(hrp, data, spec) {
    var combined = data.concat(bech32Checksum(hrp, data, spec)), str = hrp + '1', p;
    for (p = 0; p < combined.length; p++) str += BECH32.charAt(combined[p]);
    return str;
  }
  function convertBits(data, fromBits, toBits, pad) {
    var acc = 0, bits = 0, ret = [], maxv = (1 << toBits) - 1,
      maxAcc = (1 << (fromBits + toBits - 1)) - 1, i;
    for (i = 0; i < data.length; i++) {
      acc = ((acc << fromBits) | data[i]) & maxAcc;
      bits += fromBits;
      while (bits >= toBits) { bits -= toBits; ret.push((acc >>> bits) & maxv); }
    }
    if (pad && bits > 0) ret.push((acc << (toBits - bits)) & maxv);
    return ret;
  }
  function segwit(hrp, witver, program, spec) {
    return bech32Encode(hrp, [witver].concat(convertBits(program, 8, 5, true)), spec);
  }

  // ------------------------------------------------------------------ CRC16 (XMODEM, for TON)
  function crc16(bytes) {
    var crc = 0, i, j;
    for (i = 0; i < bytes.length; i++) {
      crc ^= bytes[i] << 8;
      for (j = 0; j < 8; j++) crc = (crc & 0x8000) ? (((crc << 1) ^ 0x1021) & 0xffff) : ((crc << 1) & 0xffff);
    }
    return crc & 0xffff;
  }
  var B64URL = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_';
  function base64url(bytes) {
    var out = '', i;
    for (i = 0; i < bytes.length; i += 3) {
      var b0 = bytes[i], b1 = bytes[i + 1], b2 = bytes[i + 2];
      out += B64URL.charAt(b0 >> 2);
      out += B64URL.charAt(((b0 & 3) << 4) | ((b1 === undefined ? 0 : b1) >> 4));
      if (b1 !== undefined) out += B64URL.charAt(((b1 & 15) << 2) | ((b2 === undefined ? 0 : b2) >> 6));
      if (b2 !== undefined) out += B64URL.charAt(b2 & 63);
    }
    return out;
  }

  // ------------------------------------------------------------------ 20-byte helpers
  function bytes20FromBig(n) { return hexToBytes(n.toString(16).padStart(40, '0')); }
  function expand32(h20) { return h20.concat(h20.slice(0, 12)); }               // 20 -> 32
  function expand64(h20) { return h20.concat(h20, h20, h20.slice(0, 4)); }     // 20 -> 64

  function eip55(h20) {
    var lower = bytesToHex(h20);
    var hash = bytesToHex(keccak256(strToBytes(lower)));
    var out = '';
    for (var i = 0; i < 40; i++) {
      var c = lower.charAt(i);
      out += (parseInt(hash.charAt(i), 16) >= 8) ? c.toUpperCase() : c;
    }
    return '0x' + out;
  }
  function xrpAddress(h20) {
    var body = [0x00].concat(h20);
    return sha256(strToBytes(bytesToStr(body))).then(function (h1) {
      return sha256(h1).then(function (h2) {
        return b58encode(body.concat(h2.slice(0, 4)), RIPPLE_B58);
      });
    });
  }
  function tonAddress(h32) {
    var body = [0x11, 0x00].concat(h32);
    var crc = crc16(body);
    return base64url(body.concat([(crc >> 8) & 0xff, crc & 0xff]));
  }
  function moneroAddress(h20) {
    var spend = expand32(h20), view = expand32(h20).map(function (b, i) { return i === 0 ? (b ^ 0x01) & 0xff : b; });
    var payload = [0x12].concat(spend, view);
    var chk = keccak256(payload).slice(0, 4);
    return moneroB58(payload.concat(chk));
  }

  // ------------------------------------------------------------------ CashAddr (BCH, spec v0.1)
  // Bitcoin Cash "q…" address: 5-bit base32 data + 8-symbol checksum over a
  // prefix-expanded polymod (40-bit registers). Returned WITHOUT the
  // "bitcoincash:" prefix, matching the q… form shown in the UI.
  var CASHADDR_CHARSET = 'qpzry9x8gf2tvdw0s3jn54khce6mua7l';
  var CASHADDR_GEN = [0x98f2bc8e61n, 0x79b76d99e2n, 0xf33e5fb3c4n, 0xae2eabe2a8n, 0x1e4f43e470n];
  function cashaddrPolymod(v) {
    var c = 1n, i, j;
    for (i = 0; i < v.length; i++) {
      var c0 = c >> 35n;
      c = ((c & 0x07ffffffffn) << 5n) ^ BigInt(v[i]);
      for (j = 0; j < 5; j++) if ((c0 >> BigInt(j)) & 1n) c ^= CASHADDR_GEN[j];
    }
    return c ^ 1n;
  }
  // Prefix expansion: low 5 bits of every prefix char, then a 0 separator.
  // (The high-bit half is NOT appended — this is the expansion the reference
  // encoder used, and it is what the published vectors verify against.)
  function cashaddrPrefixExpand(prefix) {
    var ret = [], i;
    for (i = 0; i < prefix.length; i++) ret.push(prefix.charCodeAt(i) & 31);
    ret.push(0);
    return ret;
  }
  function cashaddrEncode(prefix, versionByte, hash) {
    var payload = [versionByte].concat(hash);
    var data = convertBits(payload, 8, 5, true);
    var values = cashaddrPrefixExpand(prefix).concat(data).concat([0, 0, 0, 0, 0, 0, 0, 0]);
    var mod = cashaddrPolymod(values), checksum = [], i;
    for (i = 0; i < 8; i++) checksum.push(Number((mod >> BigInt(5 * (7 - i))) & 31n));
    var combined = data.concat(checksum), out = '';
    for (i = 0; i < combined.length; i++) out += CASHADDR_CHARSET.charAt(combined[i]);
    return out;
  }

  // ------------------------------------------------------------------ per-kind renderer
  // kind -> async function(bytes20[] ) -> address string
  var RENDER = {
    evm: function (h) { return Promise.resolve(eip55(h)); },
    tron: function (h) { return b58check([0x41], h); },
    xrp: function (h) { return xrpAddress(h); },
    litecoin: function (h) { return b58check([0x30], h); },          // L... P2PKH
    dogecoin: function (h) { return b58check([0x1e], h); },          // D...
    bitcoin: function (h) { return b58check([0x00], h); },           // 1... P2PKH
    bitcoin_cash: function (h) { return b58check([0x00], h); },      // 1... legacy
    bitcoin_cash_cashaddr: function (h) { return Promise.resolve(cashaddrEncode('bitcoincash', 0x00, h)); }, // q...
    zcash: function (h) { return b58check([0x1c, 0xb8], h); },       // t1...
    solana: function (h) { return Promise.resolve(b58encode(expand32(h))); },
    ton: function (h) { return Promise.resolve(tonAddress(expand32(h))); },
    sui: function (h) { return Promise.resolve('0x' + bytesToHex(expand32(h))); },
    monero: function (h) { return Promise.resolve(moneroAddress(h)); }
  };

  function renderAddress(kind, n) {
    var fn = RENDER[kind];
    var h = bytes20FromBig(n);
    if (!fn) return Promise.resolve('0x' + bytesToHex(h));
    return fn(h);
  }

  var LIB = {
    keccak256: keccak256, sha256: sha256, b58encode: b58encode, b58check: b58check,
    segwit: segwit, eip55: eip55, xrpAddress: xrpAddress, tonAddress: tonAddress,
    cashaddrEncode: cashaddrEncode,
    moneroAddress: moneroAddress, crc16: crc16, base64url: base64url,
    bytes20FromBig: bytes20FromBig, expand32: expand32, expand64: expand64,
    renderAddress: renderAddress, RENDER: RENDER, KINDS: Object.keys(RENDER),
    hexToBytes: hexToBytes, bytesToHex: bytesToHex
  };
  root.CGT_ADB_LIB = LIB;
  if (typeof module !== 'undefined' && module.exports) module.exports = LIB;
})(typeof window !== 'undefined' ? window : globalThis);
