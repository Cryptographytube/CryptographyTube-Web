/*!
 * monero-derive.js — real Monero (XMR) address derivation for private-keys/monero.html
 *
 * Why this file exists
 * --------------------
 * Monero is not one of the engine's built-in chainInfo.type branches, so with
 * type "monero" the engine falls back to an EVM-style address for each key
 * (the raw key rendered as 0x…). This patch derives the CORRECT Monero
 * standard address from every private key, entirely client-side.
 *
 * The site browses a key space where each row's private key is the integer N
 * (big-endian hex, e.g. key 1 = 000…001) — identical across every chain. This
 * patch turns that same N into a Monero address:
 *
 *   spendScalar = N mod L                       (L = ed25519 group order; sc_reduce32)
 *   secSpend    = little-endian(spendScalar)    (Monero-native scalar bytes)
 *   viewScalar  = keccak256(secSpend) mod L      (Hs — deterministic view key)
 *   pubSpend    = spendScalar · G   (ed25519)    pubView = viewScalar · G
 *   address     = base58Monero(0x12 ‖ pubSpend ‖ pubView ‖ keccak256(prefix‖pubs)[:4])
 *
 * (0x12 = mainnet standard-address tag → addresses start with "4", 95 chars.)
 * Verified against the canonical monero-python test vector (address + view key).
 *
 * How it installs
 * ---------------
 * It wraps CGT.updateAddressForRow: the original still runs (so .col-key — the
 * hex private key link + copy button, which is chain-independent — is rendered
 * exactly as on every other page), then this patch overwrites ONLY .col-address
 * with the derived Monero address in the same synchronous call (no flash).
 * Rows already rendered before install, and any later pagination re-render, are
 * covered by a one-shot sweep + a childList MutationObserver.
 *
 * It stashes each row's derived address and PRIVATE VIEW KEY on the row
 * (dataset.xmrAddr / dataset.xmrView) and exposes window.MoneroDerive.derive()
 * so monero-balance.js can reuse them without re-deriving.
 *
 * Monero has no public per-address explorer (that is the whole point of the
 * protocol), so .col-address shows the address as copyable text — no link.
 */
(function () {
  'use strict';

  var POLL_MS = 25, MAX_TRIES = 800;

  /* ------------------------------------------------------------- guards --- */
  function libsReady() {
    return !!(window.NobleHashes && window.NobleHashes.sha3Module &&
              window.NobleHashes.sha3Module.keccak_256 &&
              window.NobleCurves && window.NobleCurves.ed25519Module &&
              window.NobleCurves.ed25519Module.ed25519);
  }
  function engineReady() {
    return !!(window.CGT && typeof window.CGT.updateAddressForRow === 'function');
  }
  function isMoneroPage() {
    var c = window.CGT_CONFIG || (window.CGT && window.CGT.config) || {};
    return c.chain === 'monero';
  }

  /* ------------------------------------------- crypto primitives (once) --- */
  var _keccak, _PT, _L;
  var B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
  // base58 output length for a partial trailing block of 0..8 bytes
  var ENC = [0, 2, 3, 5, 6, 7, 9, 10, 11];

  function initCrypto() {
    _keccak = window.NobleHashes.sha3Module.keccak_256;
    var ed = window.NobleCurves.ed25519Module.ed25519;
    _PT = ed.ExtendedPoint || ed.Point;   // noble exposes ExtendedPoint
    _L = ed.CURVE.n;                       // ed25519 group order
  }

  function bytesToHex(b) { var s = ''; for (var i = 0; i < b.length; i++) s += b[i].toString(16).padStart(2, '0'); return s; }
  function leToScalar(b) { var n = 0n; for (var i = b.length - 1; i >= 0; i--) n = (n << 8n) | BigInt(b[i]); return n % _L; }
  function scalarToLe(n) { n = ((n % _L) + _L) % _L; var b = new Uint8Array(32); for (var i = 0; i < 32; i++) { b[i] = Number(n & 255n); n >>= 8n; } return b; }
  function pubFromScalar(n) { n = ((n % _L) + _L) % _L; return _PT.BASE.multiply(n === 0n ? _L : n).toRawBytes(); }
  function concatBytes() { var a = [].slice.call(arguments), len = 0, i; for (i = 0; i < a.length; i++) len += a[i].length; var r = new Uint8Array(len), o = 0; for (i = 0; i < a.length; i++) { r.set(a[i], o); o += a[i].length; } return r; }
  function encBlock(bytes) { var num = 0n, i; for (i = 0; i < bytes.length; i++) num = (num << 8n) | BigInt(bytes[i]); var outLen = ENC[bytes.length], s = '', t = num; while (t > 0n) { s = B58[Number(t % 58n)] + s; t /= 58n; } while (s.length < outLen) s = '1' + s; return s; }
  function b58encode(bytes) { var o = ''; for (var i = 0; i < bytes.length; i += 8) o += encBlock(bytes.slice(i, i + 8)); return o; }

  // privKeyHex = the site's big-endian integer key (key N). Returns the derived
  // Monero standard address and the deterministic private view key (hex).
  function derive(privKeyHex) {
    var beHex = (privKeyHex || '').replace(/^0x/, '').replace(/[^0-9a-fA-F]/g, '');
    if (!beHex) beHex = '0';
    var spendScalar = BigInt('0x' + beHex) % _L;
    var secSpend = scalarToLe(spendScalar);
    var viewScalar = leToScalar(_keccak(secSpend));
    var pubSpend = pubFromScalar(spendScalar);
    var pubView = pubFromScalar(viewScalar);
    var data = concatBytes(new Uint8Array([0x12]), pubSpend, pubView);
    var checksum = _keccak(data).slice(0, 4);
    return {
      address: b58encode(concatBytes(data, checksum)),
      viewKey: bytesToHex(scalarToLe(viewScalar))
    };
  }

  /* --------------------------------------------------------- rendering --- */
  // Copyable address text (no explorer link — Monero has no per-address lookup).
  function renderAddress(cell, address) {
    cell.innerHTML =
      '<span class="address-item">' +
        '<span class="address-link" title="Monero standard address (no public per-address explorer)">' + address + '</span>' +
        '<button class="copy-btn" onclick="CGT.copy(\'' + address + '\')" title="Copy Address">' +
          '<img src="/assets/svgs/regular/copy.svg" class="fa-icon" width="12" height="12" alt="">' +
        '</button>' +
      '</span>';
  }

  function applyToRow(row, privKeyHex) {
    var d = derive(privKeyHex);
    var cell = row.querySelector('.col-address');
    if (cell) renderAddress(cell, d.address);
    row.dataset.xmrAddr = d.address;
    row.dataset.xmrView = d.viewKey;
    return d;
  }

  // Read a row's private key straight from the rendered .col-key hex link.
  function rowHex(row) {
    var link = row.querySelector('.col-key .private-key, .col-key .key-link, .col-key a');
    var hex = link ? (link.textContent || '').trim() : '';
    return /^[0-9a-fA-F]{1,64}$/.test(hex) ? hex : '';
  }

  // Fix every currently-rendered row (idempotent — same key → same address).
  function sweep() {
    var kc = document.getElementById('keysContainer') || document;
    var rows = kc.querySelectorAll('.key-row');
    for (var i = 0; i < rows.length; i++) {
      var hex = rowHex(rows[i]);
      if (hex) { try { applyToRow(rows[i], hex); } catch (e) { /* skip bad row */ } }
    }
  }

  /* ---------------------------------------------------------- install --- */
  function install() {
    if (!engineReady() || !libsReady()) return false;   // keep polling
    if (!isMoneroPage()) return true;                    // not our page — stop
    if (window.CGT.__moneroDerive) return true;
    window.CGT.__moneroDerive = true;

    initCrypto();
    window.MoneroDerive = { derive: derive };

    // Wrap the engine's per-row address setter: original renders .col-key
    // correctly, then we replace .col-address with the real Monero address.
    var orig = window.CGT.updateAddressForRow.bind(window.CGT);
    window.CGT.updateAddressForRow = function (row, privKeyHex, addrType) {
      try { orig(row, privKeyHex, addrType); } catch (e) { /* engine fallback */ }
      try { applyToRow(row, privKeyHex); }
      catch (e) { try { console.error('[monero-derive]', e); } catch (_) {} }
    };

    // Catch rows rendered before this installed.
    sweep();

    // Catch pagination / re-renders that swap rows in #keysContainer. We watch
    // childList only (not subtree), so our own .col-address edits never re-fire.
    var kc = document.getElementById('keysContainer');
    if (kc && window.MutationObserver) {
      var pending = null;
      new MutationObserver(function () {
        if (pending) return;
        pending = setTimeout(function () { pending = null; sweep(); }, 0);
      }).observe(kc, { childList: true });
    }

    try { console.log('[monero-derive] installed'); } catch (e) {}
    return true;
  }

  if (!install()) {
    var tries = 0;
    var iv = setInterval(function () {
      if (install() || ++tries > MAX_TRIES) clearInterval(iv);
    }, POLL_MS);
  }
})();
