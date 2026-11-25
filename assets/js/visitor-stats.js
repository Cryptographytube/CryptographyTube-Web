/* ============================================================================
   visitor-stats.js  —  home-page live / total visitor counter (per-domain)

   Renders TWO real numbers into #cgt-visitor-stat as "live / total".
   No label words anywhere (owner directive): the box shows only the numbers.

     live  = people with the site open right now (real-time presence)
     total = cumulative visitors ever (persisted server-side, never resets)

   Data comes from same-origin ./stats.php (see that file). This script only
   displays what the server returns; if the endpoint is unavailable (e.g. the
   local dev server serves raw PHP), it shows nothing rather than fake numbers.
   ============================================================================ */
(function () {
    'use strict';

    var EL_ID   = 'cgt-visitor-stat';
    var POLL_MS = 30000;              // re-ping every 30s (inside the server's 90s window; light on shared hosting)
    var ENDPOINT = './stats.php';

    /* Stable-per-tab client id so the server can track presence without a login. */
    function clientId() {
        try {
            var k = 'cgtVid', v = sessionStorage.getItem(k);
            if (!v) {
                v = (Date.now().toString(36) + Math.random().toString(36).slice(2, 10)).slice(0, 24);
                sessionStorage.setItem(k, v);
            }
            return v;
        } catch (e) {
            return 'nc' + Math.random().toString(36).slice(2, 12);
        }
    }

    function fmt(n) {
        try { return Number(n).toLocaleString('en-US'); } catch (e) { return String(n); }
    }

    var elLive, elTotal, id = clientId(), timer = null, stopped = false;

    function paint(live, total) {
        if (elLive)  elLive.textContent  = fmt(live);
        if (elTotal) elTotal.textContent = fmt(total);
    }

    function poll() {
        if (stopped) return;
        var url = ENDPOINT + '?id=' + encodeURIComponent(id) + '&t=' + Date.now();
        fetch(url, { credentials: 'same-origin', cache: 'no-store' })
            .then(function (r) { return r.ok ? r.json() : null; })
            .then(function (d) {
                if (d && d.ok) { paint(d.live, d.total); }
            })
            .catch(function () { /* endpoint down -> leave last real value, never fake */ });
    }

    function start() {
        var host = document.getElementById(EL_ID);
        if (!host) return;
        elLive  = host.querySelector('[data-stat="live"]');
        elTotal = host.querySelector('[data-stat="total"]');
        poll();
        timer = setInterval(poll, POLL_MS);

        // Pause polling when the tab is hidden so we don't count idle background tabs as "live".
        document.addEventListener('visibilitychange', function () {
            if (document.hidden) {
                stopped = true;
                if (timer) { clearInterval(timer); timer = null; }
            } else if (stopped) {
                stopped = false;
                poll();
                timer = setInterval(poll, POLL_MS);
            }
        });
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', start);
    } else {
        start();
    }
})();
