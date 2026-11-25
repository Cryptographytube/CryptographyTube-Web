/* ============================================================================
   luck-found.js  —  Luck Puzzle auto-scan + global "Found Luck" capture.

   Loaded ONLY on /luck-puzzle/<chain> pages (injected by _build_luck_puzzle.py).

   What it does, with zero clicks from the visitor:
     1. Starts the Range Scan engine automatically (Auto + Random) and keeps it
        running page after page, so every address on the page is checked.
     2. Watches the key rows. The moment a row shows ANY on-chain activity
        (balance > 0 OR received > 0 OR tx > 0) it reads that row's address AND
        its private key and POSTs them to found.php, where they are stored
        forever and shown to everyone on /luck-puzzle/found.
     3. Keeps a live "Found Luck (N)" button in the scan bar linking to the
        dashboard.

   REAL findings only. Nothing here invents a hit: a record is sent only when
   the page's own balance engine actually marked a row active and filled in a
   positive balance / received / tx value. With random keys a hit is ~1 in 2^160,
   so the board will normally stay empty — that is correct, not a failure.

   The Range Scan engine (assets/js/range-scan.js) is used as-is and is never
   modified; this file only reads the DOM it produces.
   ============================================================================ */
(function () {
  'use strict';

  if (window.__CGT_LUCK_FOUND__) return;   // never double-bind
  window.__CGT_LUCK_FOUND__ = true;

  // ---- only on a Luck Puzzle chain page ------------------------------------
  var m = /^\/luck-puzzle\/([a-z0-9-]+)\/?$/i.exec(location.pathname);
  if (!m) return;
  var CHAIN = m[1].toLowerCase();
  if (CHAIN === 'found') return;           // the dashboard itself
  var ENDPOINT = '/found.php';

  var SCAN_TICK_MS   = 5000;    // how often we re-check a running scan
  var COUNT_POLL_MS  = 30000;   // dashboard counter refresh
  var OBSERVE_MS     = 1500;    // debounce for DOM-mutation bursts

  var userStopped = false;      // the visitor pressed Stop themselves -> respect it
  var pausedByUs  = false;      // we paused because the tab went to the background
  var selfActing  = false;      // we are the ones clicking Stop right now
  var scanKicked  = false;
  var sent        = Object.create(null);   // client-side dedup: chain|address
  var pending     = Object.create(null);

  function $(id) { return document.getElementById(id); }

  /* ---------------------------------------------------------------- dedup -- */
  // Persisted so a reload does not re-POST the same finding. The server also
  // dedups (found-data/index.txt), so this is only a courtesy to the network.
  var LS_KEY = 'cgt_luckfound_sent_v1';
  try {
    var saved = JSON.parse(localStorage.getItem(LS_KEY) || '[]');
    if (Array.isArray(saved)) { for (var i = 0; i < saved.length; i++) sent[saved[i]] = 1; }
  } catch (e) {}

  function markSent(key) {
    sent[key] = 1;
    try {
      var keys = Object.keys(sent);
      if (keys.length > 2000) {                 // keep localStorage bounded
        keys = keys.slice(keys.length - 2000);
        sent = Object.create(null);
        for (var i = 0; i < keys.length; i++) sent[keys[i]] = 1;
      }
      localStorage.setItem(LS_KEY, JSON.stringify(Object.keys(sent)));
    } catch (e) {}
  }

  /* ---------------------------------------------------------------- sizing -- */
  function compact(s) {
    s = String(s == null ? '' : s).replace(/\s+/g, ' ').trim();
    return s.length > 48 ? s.slice(0, 48) : s;
  }

  // A cell value counts only if it carries the engine's own "found" marker OR
  // holds a positive number. Spinners / "0" / "-" / "Error" never count.
  function isPositive(el) {
    if (!el) return false;
    if (el.classList.contains('has-balance') ||
        el.classList.contains('has-recv') ||
        el.classList.contains('has-tx')) return true;
    var t = (el.textContent || '').replace(/[^0-9.]/g, '');
    if (!t) return false;
    var v = parseFloat(t);
    return isFinite(v) && v > 0;
  }

  function firstText(root, sels) {
    for (var i = 0; i < sels.length; i++) {
      var el = root.querySelector(sels[i]);
      if (el) {
        var t = (el.textContent || '').trim();
        if (t) return t;
      }
    }
    return '';
  }

  /* --------------------------------------------------------------- harvest -- */
  // Returns array of {addr, wif, bal, recv, tx} for every ACTIVE address in the
  // row. A row can carry several address variants (legacy c/u, segwit, …), each
  // with its own balance-info span, so each variant is reported with the value
  // that belongs to it.
  function harvestRow(row) {
    var hexEl = row.querySelector('.private-key');
    var hex = hexEl ? (hexEl.textContent || '').trim() : '';
    if (!/^[0-9a-fA-F]{64}$/.test(hex)) return [];

    var wif = firstText(row, ['.wif-value', '.wif']);
    // WIF markup: <span class="wif-label">(u)</span><span class="wif-value key-link">…</span>
    var addrWrap = row.querySelector('.col-address') || row;
    var items = addrWrap.querySelectorAll('.address-item');
    var out = [];

    if (items.length) {
      for (var i = 0; i < items.length; i++) {
        var it = items[i];
        var addr = '';
        var a = it.querySelector('.address-link, a[href]');
        if (a) addr = (a.textContent || '').trim();
        if (!addr) {
          var s = it.querySelector('.address-text');
          if (s) addr = (s.textContent || '').trim();
        }
        if (!addr) continue;

        // The matching value cell for this variant: the nearest .col-balance only
        // holds ALL variants, so prefer a per-item .balance-info when present.
        var scope = it.closest('li, tr, .addr-row') || null;
        var info = it.querySelector('.balance-info') || (scope && scope.querySelector('.balance-info'));
        var balEl = info ? info.querySelector('.bal, .balance-value') : null;
        var recvEl = info ? info.querySelector('.recv') : null;
        var txEl = info ? info.querySelector('.tx') : null;
        if (!info) {
          var col = row.querySelector('.col-balance');
          balEl = col ? col.querySelector('.bal') : null;
          recvEl = col ? col.querySelector('.recv') : null;
          txEl = col ? col.querySelector('.tx') : null;
        }

        var bal = balEl ? compact(balEl.textContent) : '';
        var recv = recvEl ? compact(recvEl.textContent) : '';
        var tx = txEl ? compact(txEl.textContent) : '';

        if (isPositive(balEl) || isPositive(recvEl) || isPositive(txEl) ||
            row.classList.contains('has-balance') || row.classList.contains('was-active')) {
          // Row-level "active" alone is not proof for THIS variant, so accept it
          // only when that variant's own cell looks positive.
          if (isPositive(balEl) || isPositive(recvEl) || isPositive(txEl)) {
            out.push({ addr: addr, wif: wif, bal: bal || '0', recv: recv || '0', tx: tx || '0' });
          }
        }
      }
    }

    // Fallback: no .address-item markup (plain .col-address text) but the row is
    // active and the single address is positive.
    if (!out.length) {
      var col = row.querySelector('.col-balance');
      var balEl2 = col ? col.querySelector('.bal') : null;
      var recvEl2 = col ? col.querySelector('.recv') : null;
      var txEl2 = col ? col.querySelector('.tx') : null;
      var active = row.classList.contains('has-balance') ||
                   (col && col.classList.contains('has-balance')) ||
                   isPositive(balEl2) || isPositive(recvEl2) || isPositive(txEl2);
      if (active) {
        var txt = '';
        var at = addrWrap.querySelector('.address-text');
        if (at) txt = (at.textContent || '').trim();
        if (!txt) {
          // .col-address may hold bare text with the copy button next to it
          txt = (addrWrap.textContent || '').trim();
        }
        // strip a leading type tag like "(u) " and any copy-button noise
        txt = txt.replace(/^\([a-zA-Z0-9+/=-]{1,8}\)\s*/, '').split(/\s+/)[0];
        if (txt && /^[A-Za-z0-9]{20,120}$/.test(txt)) {
          out.push({
            addr: txt, wif: wif,
            bal: balEl2 ? compact(balEl2.textContent) : '0',
            recv: recvEl2 ? compact(recvEl2.textContent) : '0',
            tx: txEl2 ? compact(txEl2.textContent) : '0'
          });
        }
      }
    }

    // last resort: row marked active but we could not read a clean address
    if (!out.length) return [];
    for (var k = 0; k < out.length; k++) out[k].hex = hex;
    return out;
  }

  /* ------------------------------------------------------------------ send -- */
  function send(rec) {
    var key = CHAIN + '|' + rec.addr;
    if (sent[key] || pending[key]) return;
    pending[key] = 1;

    var payload = {
      chain: CHAIN, address: rec.addr, pk_hex: rec.hex, wif: rec.wif || '',
      bal: rec.bal || '', recv: rec.recv || '', tx: rec.tx || ''
    };

    fetch(ENDPOINT, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
      keepalive: true
    }).then(function (r) { return r.json(); }).then(function (res) {
      delete pending[key];
      if (res && res.ok) {
        markSent(key);
        bumpBadge(res.total);
      }
    }).catch(function () {
      delete pending[key];   // network hiccup: retry on the next observation
    });
  }

  /* ------------------------------------------------------------ DOM watch -- */
  var obsTimer = null;

  function sweep() {
    var host = $('keysContainer');
    if (!host) return;
    var rows = host.querySelectorAll('.key-row');
    for (var i = 0; i < rows.length; i++) {
      var row = rows[i];
      var active = row.classList.contains('has-balance') ||
                   row.classList.contains('was-active') ||
                   row.querySelector('.col-balance .has-balance, .col-balance .has-recv, .col-balance .has-tx');
      if (!active) continue;
      var recs = harvestRow(row);
      for (var j = 0; j < recs.length; j++) send(recs[j]);
    }
  }

  function onMutations() {
    if (obsTimer) return;
    obsTimer = setTimeout(function () { obsTimer = null; sweep(); }, OBSERVE_MS);
  }

  function startObserver() {
    var host = $('keysContainer');
    if (!host || !window.MutationObserver) return;
    new MutationObserver(onMutations).observe(host, {
      childList: true, subtree: true, attributes: true, characterData: true,
      attributeFilter: ['class', 'data-balance-fetched']
    });
    // The engine also swaps rows in place; a slow periodic sweep catches any row
    // whose final value landed without a further mutation.
    setInterval(sweep, 10000);
  }

  /* ------------------------------------------------------- auto-start scan -- */
  function scanRunning() {
    var stop = $('btn-range-stop');
    return !!(stop && stop.style.display !== 'none');
  }

  function autoStart() {
    var startBtn = $('btn-range-start');
    var stopBtn = $('btn-range-stop');
    if (!startBtn || !stopBtn) return false;

    // Continuous + random pages: keep it crawling with no clicks.
    var auto = $('rangeAuto');
    if (auto && !auto.checked) {
      auto.checked = true;
      auto.dispatchEvent(new Event('change', { bubbles: true }));
    }
    var rnd = $('rangeRandom');
    if (rnd && !rnd.checked) {
      rnd.checked = true;
      rnd.dispatchEvent(new Event('change', { bubbles: true }));
    }

    if (!scanRunning()) {
      scanKicked = true;
      startBtn.click();
    }
    return true;
  }

  function bindStopWatch() {
    var stopBtn = $('btn-range-stop');
    if (!stopBtn || stopBtn.__cgtStopBound) return;
    stopBtn.__cgtStopBound = true;
    stopBtn.addEventListener('click', function () {
      if (selfActing) return;            // our own background pause
      userStopped = true;                // the visitor chose to stop
    }, true);
  }

  function tick() {
    bindStopWatch();
    if (userStopped) return;

    var hidden = document.hidden;
    if (hidden) {
      // Do not burn API calls on a background tab.
      if (scanRunning()) {
        pausedByUs = true;
        selfActing = true;
        var sb = $('btn-range-stop');
        if (sb) sb.click();
        setTimeout(function () { selfActing = false; }, 0);
      }
      return;
    }

    if (!scanRunning()) {
      if (pausedByUs) pausedByUs = false;
      autoStart();
    }
  }

  function visibilityChange() {
    if (!document.hidden && !userStopped && !scanRunning()) autoStart();
  }

  /* --------------------------------------------------------------- badge ---- */
  function bumpBadge(total) {
    var b = $('cgtFoundLuckBtn');
    if (!b || typeof total !== 'number') return;
    var n = b.querySelector('.cgt-fl-count');
    if (n) n.textContent = total.toLocaleString();
  }

  function pollCount() {
    fetch(ENDPOINT + '?count=1', { cache: 'no-store' })
      .then(function (r) { return r.json(); })
      .then(function (res) {
        if (res && res.ok) bumpBadge(res.total);   // keep the last known value on failure
      })
      .catch(function () {});
  }

  function injectButton() {
    if ($('cgtFoundLuckBtn')) return true;
    var bar = $('rangeScanBar');
    if (!bar) return false;

    var wrap = document.createElement('div');
    wrap.className = 'cgt-found-luck-bar';
    wrap.style.cssText = 'display:flex;justify-content:flex-end;margin:0 0 8px 0;';
    wrap.innerHTML =
      '<a id="cgtFoundLuckBtn" href="/luck-puzzle/found" ' +
      'style="display:inline-flex;align-items:center;gap:6px;padding:6px 12px;border-radius:8px;' +
      'font-size:13px;font-weight:600;text-decoration:none;background:#f7931a;color:#fff;">' +
      '🏆 Found Luck (<span class="cgt-fl-count">0</span>)</a>';

    var head = bar.querySelector('.range-scan-head');
    if (head && head.parentNode) head.parentNode.insertBefore(wrap, head);
    else bar.insertBefore(wrap, bar.firstChild);

    pollCount();
    return true;
  }

  /* ------------------------------------------------------------------ boot -- */
  function boot() {
    var tries = 0;
    var t = setInterval(function () {
      tries++;
      var okBar = injectButton();
      var okStart = autoStart();
      if (okBar && okStart) {
        clearInterval(t);
        startObserver();
        bindStopWatch();
        setInterval(tick, SCAN_TICK_MS);
        document.addEventListener('visibilitychange', visibilityChange);
        pollCount();
        setInterval(pollCount, COUNT_POLL_MS);
      }
      if (tries > 200) clearInterval(t);   // give up after ~60s if the page never fills in
    }, 300);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }
})();
