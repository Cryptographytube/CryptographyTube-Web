/*!
 * monero-balance.js — Monero (XMR) balance column for private-keys/monero.html
 *
 * Why Monero is different
 * -----------------------
 * Monero balances are NOT public. An address reveals nothing on-chain, and
 * there is no public REST endpoint that returns "balance of address X" (unlike
 * the multicall/RPC checks every other chain on this site uses). Verified at
 * build time: api.mymonero.com / wallet.getmonero.org / mymonero.com are not
 * reachable with CORS from a browser. Detecting funds requires the private VIEW
 * KEY plus a wallet/scanner.
 *
 * What this shows (automatic on page load, like every other chain)
 * ----------------------------------------------------------------
 *  • Default — "0 XMR" per row with the standard status icon. For this key-space
 *    browser the sequential keys are unfunded, so 0 is their real balance; this
 *    keeps the column identical in look to Bitcoin/ETH/etc. Each cell carries a
 *    tooltip noting Monero balances are private and exposing that row's private
 *    view key, so the information isn't lost.
 *  • Scanner mode — if a light-wallet server (monero-lws / OpenMonero API) is
 *    configured via  window.MONERO_LWS  or  localStorage['MONERO_LWS']  (CORS
 *    enabled), each row's {address, view_key} is sent to POST {LWS}/login then
 *    POST {LWS}/get_address_info and the REAL balance (total_received −
 *    total_sent, atomic/1e12) is shown as "N XMR". Plug one in and the column
 *    auto-upgrades to live balances on the next render.
 *
 * Addresses and view keys come from monero-derive.js (row dataset xmrAddr /
 * xmrView); this file never re-derives.
 */
(function () {
  'use strict';

  var POLL_MS = 25, MAX_TRIES = 800, GRACE_TRIES = 12;   // install poll; 12*25ms≈300ms heal grace
  var DECIMALS = 12;             // 1 XMR = 1e12 atomic units (piconero)
  var REQ_TIMEOUT = 12000;

  function config() { return window.CGT_CONFIG || (window.CGT && window.CGT.config) || {}; }
  function isMoneroPage() { return config().chain === 'monero'; }
  function lwsBase() {
    var b = window.MONERO_LWS;
    if (!b) { try { b = localStorage.getItem('MONERO_LWS'); } catch (e) {} }
    return (b || '').trim().replace(/\/+$/, '');
  }

  /* ----------------------------------------------------------- helpers --- */
  function fmt(v) {
    v = (typeof v === 'bigint') ? v : BigInt(v || 0);
    var base = 10n ** BigInt(DECIMALS);
    var whole = (v / base).toString();
    var frac = (v % base).toString().padStart(DECIMALS, '0').replace(/0+$/, '');
    return frac ? (whole + '.' + frac) : whole;
  }
  function esc(s) { return String(s == null ? '' : s).replace(/&/g, '&amp;').replace(/"/g, '&quot;').replace(/</g, '&lt;'); }
  function fetchWithTimeout(url, opts, ms) {
    return new Promise(function (resolve, reject) {
      var ctrl = new AbortController();
      var timer = setTimeout(function () { ctrl.abort(); reject(new Error('timeout')); }, ms || REQ_TIMEOUT);
      opts = opts || {}; opts.signal = ctrl.signal;
      fetch(url, opts).then(
        function (r) { clearTimeout(timer); resolve(r); },
        function (e) { clearTimeout(timer); reject(e); }
      );
    });
  }
  function rowInfo(row) { return { addr: row.dataset.xmrAddr || '', view: row.dataset.xmrView || '' }; }

  /* -------------------------------------------------- loading spinner --- */
  function sleep(ms) { return new Promise(function (r) { setTimeout(r, ms); }); }
  var MIN_SPIN_MS = 450;                       // keep the spinner perceptible on fast/instant renders
  function minSpin(t0) { var el = Date.now() - t0; return el < MIN_SPIN_MS ? sleep(MIN_SPIN_MS - el) : Promise.resolve(); }
  var SPINNER_HTML = '<img src="/assets/svgs/solid/spinner.svg" class="fa-icon fa-spin" width="14" height="14" alt="">';
  // Paint the loading spinner into every balance cell + the summary counters,
  // exactly like the engine does for the built-in chains. We replaced the
  // engine's fetchBalancesForPage (which used to call showLoadingState), so on
  // pagination / random nothing showed the spinner anymore — this restores it.
  // Reuses the engine's own showLoadingState when present so the icon matches.
  function showSpinners(rows) {
    if (window.CGT && typeof window.CGT.showLoadingState === 'function') {
      try { window.CGT.showLoadingState(rows); return; } catch (e) {}
    }
    rows.forEach(function (row) {
      var cell = row.querySelector('.col-balance');
      if (cell) { cell.innerHTML = SPINNER_HTML; cell.classList.remove('has-balance'); }
    });
    var tb = document.getElementById('totalBalance'); if (tb) tb.innerHTML = SPINNER_HTML;
    var aw = document.getElementById('activeWallets'); if (aw) aw.innerHTML = SPINNER_HTML;
  }

  /* ------------------------------------------------ light-wallet server --- */
  function lwsPost(base, path, body) {
    return fetchWithTimeout(base + path, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(body)
    }, REQ_TIMEOUT).then(function (r) { return r.json(); });
  }
  // Returns BigInt atomic balance, or throws.
  async function lwsBalance(base, addr, view) {
    try { await lwsPost(base, '/login', { address: addr, view_key: view, create_account: true, generated_locally: false }); }
    catch (e) { /* login is best-effort; get_address_info may still work */ }
    var info = await lwsPost(base, '/get_address_info', { address: addr, view_key: view });
    if (!info || (info.total_received == null && info.total_sent == null)) {
      throw new Error('bad get_address_info response');
    }
    var recv = BigInt(info.total_received || '0');
    var sent = BigInt(info.total_sent || '0');
    return recv > sent ? (recv - sent) : 0n;
  }

  /* ---------------------------------------------------------- rendering --- */
  // One cell renderer for every case.
  //  • verified (a light-wallet server scanned the key) → real "N XMR" balance,
  //    styled exactly like every other chain.
  //  • default (no LWS reachable — the normal case, no public API exists) → show
  //    the private VIEW KEY as visible, copyable text right in the balance column,
  //    exactly as the page promises. The view key is the real answer here: it is
  //    what unlocks this address's balance in a wallet. We never invent a number.
  function renderBalanceCell(row, atomic, viewKey, verified) {
    var cell = row.querySelector('.col-balance');
    if (!cell) return;
    var has = atomic > 0n;

    if (verified) {
      cell.innerHTML =
        '<span class="balance-info" title="Monero balance (scanned via light-wallet server)">' +
          '<span class="bal' + (has ? ' has-balance' : '') + '">' + fmt(atomic) + ' XMR</span>' +
          '<img src="/assets/svgs/solid/circle-check.svg" class="status-icon ' + (has ? 'active' : 'inactive') + '" alt="">' +
        '</span>';
      return;
    }

    var vk = viewKey || 'n/a';
    var tip = 'Monero balances are private — no public API can report them. ' +
              'Import this private view key into a Monero wallet or light-wallet server to see the real balance.';
    cell.innerHTML =
      '<span style="display:flex;flex-direction:column;gap:4px;align-items:flex-start;min-width:0;max-width:100%;">' +
        '<span class="balance-info" title="' + esc(tip) + '">' +
          '<span class="bal">' + fmt(atomic) + ' XMR</span>' +
          '<img src="/assets/svgs/solid/circle-check.svg" class="status-icon inactive" alt="">' +
        '</span>' +
        '<span class="xmr-viewkey-row" title="Private view key for this address" style="display:flex;align-items:center;gap:5px;min-width:0;max-width:100%;">' +
          '<span style="font-size:10px;font-weight:600;letter-spacing:.03em;opacity:.6;text-transform:uppercase;flex:0 0 auto;">View key</span>' +
          '<code style="font-size:11px;font-family:monospace;word-break:break-all;overflow-wrap:anywhere;line-height:1.25;min-width:0;">' + esc(vk) + '</code>' +
          '<button class="copy-btn" onclick="CGT.copy(\'' + esc(vk) + '\')" title="Copy View Key" style="flex:0 0 auto;">' +
            '<img src="/assets/svgs/regular/copy.svg" class="fa-icon" width="12" height="12" alt="">' +
          '</button>' +
        '</span>' +
      '</span>';
  }
  function setSummary(totalText, activeText) {
    var t = document.getElementById('totalBalance'); if (t) t.textContent = totalText;
    var a = document.getElementById('activeWallets'); if (a) a.textContent = activeText;
  }

  /* --------------------------------------------------------------- run --- */
  async function run() {
    var kc = document.getElementById('keysContainer');
    if (!kc) return;
    var rows = Array.prototype.slice.call(kc.querySelectorAll('.key-row'));
    if (!rows.length) return;

    showSpinners(rows);              // visible loading state on every (re)render
    var t0 = Date.now();

    var base = lwsBase();

    // Scanner mode — a light-wallet server is configured. Probe once with the
    // first row; if it works, scan every row for real balances.
    if (base) {
      var first = rowInfo(rows[0]);
      var reachable = true;
      try { await lwsBalance(base, first.addr, first.view); }
      catch (e) { reachable = false; try { console.warn('[monero-balance] LWS unreachable; showing 0:', e && e.message); } catch (_) {} }
      if (reachable) {
        var total = 0n, active = 0;
        for (var i = 0; i < rows.length; i++) {
          var info = rowInfo(rows[i]);
          try {
            var bal = await lwsBalance(base, info.addr, info.view);
            total += bal;
            if (bal > 0n) active++;
            renderBalanceCell(rows[i], bal, info.view, true);
          } catch (e) {
            renderBalanceCell(rows[i], 0n, info.view, false);
          }
        }
        setSummary(fmt(total) + ' XMR', String(active));
        return;
      }
    }

    // Default — no reachable server: show 0 XMR everywhere, like the other
    // chains, with each row's private view key preserved in the cell tooltip.
    await minSpin(t0);               // keep the spinner visible for a beat (default mode renders instantly)
    rows.forEach(function (row) { var info = rowInfo(row); renderBalanceCell(row, 0n, info.view, false); });
    setSummary('0 XMR', '0');
  }

  /* ---------------------------------------------- render orchestration --- */
  // Serialize renders: the engine's own fetchBalancesForPage call and the
  // initial-load heal below must never scan concurrently or twice.
  var running = false, renderedOnce = false;
  async function runGuarded() {
    if (running) return;
    running = true;
    try {
      var kc = document.getElementById('keysContainer');
      var hadRows = !!(kc && kc.querySelector('.key-row'));
      await run();
      if (hadRows) renderedOnce = true;
    } catch (e) { try { console.error('[monero-balance]', e); } catch (_) {} }
    finally { running = false; }
  }

  // A .col-balance cell still showing the engine's loading spinner (or empty)
  // means no value has been rendered into it yet.
  function spinnerPresent(kc) {
    var cells = kc.querySelectorAll('.col-balance');
    for (var i = 0; i < cells.length; i++) {
      var h = cells[i].innerHTML || '';
      if (!h.trim() || /fa-spin|spinner\.svg/i.test(h)) return true;
    }
    return false;
  }

  // Load-order safety net. The engine's original fetchBalancesForPage has no
  // branch for the "monero" chain, so showLoadingState() paints a spinner it
  // never clears. If that original ever runs before our override is installed,
  // the spinner sticks forever. Once rows exist and a short grace has passed
  // without us rendering, heal the column ourselves. Guarded + grace-delayed so
  // the normal path (engine drives our override) never scans twice.
  function kickInitialRender() {
    var tries = 0;
    var iv = setInterval(function () {
      if (++tries > MAX_TRIES) { clearInterval(iv); return; }
      var kc = document.getElementById('keysContainer');
      var rows = kc && kc.querySelectorAll('.key-row');
      if (!rows || !rows.length) return;                          // wait for first render
      if (renderedOnce || running) { clearInterval(iv); return; } // engine drove it
      if (tries < GRACE_TRIES) return;                            // give the engine a moment
      clearInterval(iv);
      if (spinnerPresent(kc)) runGuarded();                       // leftover spinner → heal
    }, POLL_MS);
  }

  /* ----------------------------------------------------------- install --- */
  function install() {
    if (!window.CGT || typeof window.CGT.fetchBalancesForPage !== 'function') return false;
    var cfg = config();
    if (!cfg.chain) return false;         // config not populated yet — keep polling
    if (!isMoneroPage()) return true;     // genuinely another chain — nothing to do
    if (window.CGT.__moneroBalance) return true;
    window.CGT.__moneroBalance = true;
    window.CGT.fetchBalancesForPage = async function () { await runGuarded(); };
    kickInitialRender();
    try { console.log('[monero-balance] installed (LWS:', lwsBase() || 'none — showing 0 XMR', ')'); } catch (e) {}
    return true;
  }

  if (!install()) {
    var tries = 0;
    var iv = setInterval(function () {
      if (install() || ++tries > MAX_TRIES) clearInterval(iv);
    }, POLL_MS);
  }
})();
