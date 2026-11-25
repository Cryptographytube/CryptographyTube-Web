/* ============================================================================
   community/js/community.js  —  front-end for the anonymous discussion board.

   Talks to ./api.php (same-origin). ALL user-supplied text is rendered with
   textContent / DOM nodes — never innerHTML — so stored content can never
   execute as markup. Routing is hash-based:  #t/<id> opens a thread, otherwise
   the thread list is shown.
   ============================================================================ */
(function () {
    'use strict';

    var API = './api.php';
    var root, newForm;

    /* ---- helpers ---------------------------------------------------------- */
    function el(tag, cls, text) {
        var n = document.createElement(tag);
        if (cls) { n.className = cls; }
        if (text != null) { n.textContent = text; }
        return n;
    }

    function timeAgo(ts) {
        if (!ts) { return ''; }
        var s = Math.max(0, Math.floor(Date.now() / 1000) - ts);
        if (s < 60) { return s + 's ago'; }
        var m = Math.floor(s / 60); if (m < 60) { return m + 'm ago'; }
        var h = Math.floor(m / 60); if (h < 24) { return h + 'h ago'; }
        var d = Math.floor(h / 24); if (d < 30) { return d + 'd ago'; }
        try { return new Date(ts * 1000).toLocaleDateString(); } catch (e) { return d + 'd ago'; }
    }

    function api(action, opts) {
        opts = opts || {};
        var url = API + '?action=' + encodeURIComponent(action);
        if (opts.query) { url += opts.query; }
        var init = { method: opts.method || 'GET', cache: 'no-store' };
        if (opts.body) {
            init.method = 'POST';
            init.headers = { 'Content-Type': 'application/x-www-form-urlencoded;charset=UTF-8' };
            init.body = opts.body;
        }
        return fetch(url, init).then(function (r) { return r.json(); });
    }

    function form(obj) {
        return Object.keys(obj).map(function (k) {
            return encodeURIComponent(k) + '=' + encodeURIComponent(obj[k]);
        }).join('&');
    }

    function setBusy(btn, busy, label) {
        if (!btn) { return; }
        btn.disabled = busy;
        if (busy) { btn.dataset._t = btn.textContent; btn.textContent = label || 'Working…'; }
        else if (btn.dataset._t) { btn.textContent = btn.dataset._t; }
    }

    function notice(msg, kind) {
        var box = document.getElementById('community-notice');
        if (!box) { return; }
        box.textContent = msg || '';
        box.className = msg ? ('alert alert-' + (kind || 'danger') + ' small mt-2') : '';
        box.style.display = msg ? '' : 'none';
    }

    /* ---- list view -------------------------------------------------------- */
    function showList() {
        if (newForm) { newForm.style.display = ''; }
        notice('');
        root.textContent = '';
        root.appendChild(el('div', 'text-muted small', 'Loading discussions…'));

        api('list', { query: '&limit=50' }).then(function (res) {
            root.textContent = '';
            if (!res || !res.ok) { root.appendChild(el('div', 'alert alert-warning small', 'Could not load discussions.')); return; }

            var head = el('div', 'd-flex align-items-center justify-content-between mb-2');
            head.appendChild(el('span', 'text-muted small', (res.total || 0) + ' discussion' + (res.total === 1 ? '' : 's')));
            root.appendChild(head);

            if (!res.items || !res.items.length) {
                root.appendChild(el('div', 'cm-empty text-muted', 'No discussions yet — start the first one above.'));
                return;
            }
            var list = el('div', 'cm-list');
            res.items.forEach(function (t) {
                var card = el('a', 'cm-card');
                card.href = '#t/' + encodeURIComponent(t.id);
                card.appendChild(el('div', 'cm-card-title', t.title));
                if (t.preview) { card.appendChild(el('div', 'cm-card-preview', t.preview)); }
                var meta = el('div', 'cm-card-meta');
                meta.appendChild(el('span', 'cm-nick', t.nick || 'anon'));
                meta.appendChild(el('span', null, '• ' + timeAgo(t.last_ts || t.ts)));
                var rc = el('span', 'cm-replies', (t.replies || 0) + ' repl' + (t.replies === 1 ? 'y' : 'ies'));
                meta.appendChild(rc);
                card.appendChild(meta);
                list.appendChild(card);
            });
            root.appendChild(list);
        }).catch(function () {
            root.textContent = '';
            root.appendChild(el('div', 'alert alert-warning small', 'Network error — try again.'));
        });
    }

    /* ---- thread view ------------------------------------------------------ */
    function showThread(id) {
        if (newForm) { newForm.style.display = 'none'; }
        notice('');
        root.textContent = '';
        root.appendChild(el('div', 'text-muted small', 'Loading…'));

        api('thread', { query: '&id=' + encodeURIComponent(id) }).then(function (res) {
            root.textContent = '';
            if (!res || !res.ok) {
                root.appendChild(el('div', 'alert alert-warning small', 'Discussion not found.'));
                root.appendChild(backLink());
                return;
            }
            root.appendChild(backLink());

            var t = res.thread;
            var op = el('div', 'cm-post cm-op');
            op.appendChild(el('h2', 'cm-post-title', t.title));
            var opMeta = el('div', 'cm-post-meta');
            opMeta.appendChild(el('span', 'cm-nick', t.nick || 'anon'));
            opMeta.appendChild(el('span', null, '• ' + timeAgo(t.ts)));
            op.appendChild(opMeta);
            op.appendChild(bodyNode(t.body));
            root.appendChild(op);

            var repWrap = el('div', 'cm-replies-wrap');
            repWrap.appendChild(el('div', 'cm-replies-head text-muted small', (res.replies.length) + ' repl' + (res.replies.length === 1 ? 'y' : 'ies')));
            res.replies.forEach(function (r) {
                var p = el('div', 'cm-post');
                var m = el('div', 'cm-post-meta');
                m.appendChild(el('span', 'cm-nick', r.nick || 'anon'));
                m.appendChild(el('span', null, '• ' + timeAgo(r.ts)));
                p.appendChild(m);
                p.appendChild(bodyNode(r.body));
                repWrap.appendChild(p);
            });
            root.appendChild(repWrap);
            root.appendChild(replyForm(id));
        }).catch(function () {
            root.textContent = '';
            root.appendChild(el('div', 'alert alert-warning small', 'Network error — try again.'));
            root.appendChild(backLink());
        });
    }

    function backLink() {
        var a = el('a', 'cm-back small text-decoration-none', '← All discussions');
        a.href = '#';
        return a;
    }

    /* Render multi-line body as text with <br> breaks, safely (no innerHTML). */
    function bodyNode(text) {
        var wrap = el('div', 'cm-post-body');
        String(text == null ? '' : text).split('\n').forEach(function (line, i) {
            if (i) { wrap.appendChild(document.createElement('br')); }
            wrap.appendChild(document.createTextNode(line));
        });
        return wrap;
    }

    function replyForm(id) {
        var box = el('form', 'cm-form cm-reply-form');
        box.appendChild(el('label', 'form-label small text-muted mb-1', 'Add a reply'));

        var nick = el('input', 'form-control form-control-sm mb-2');
        nick.type = 'text'; nick.placeholder = 'Name (optional)'; nick.maxLength = 32; nick.autocomplete = 'off';

        var body = el('textarea', 'form-control form-control-sm mb-2');
        body.rows = 3; body.placeholder = 'Write a reply…'; body.maxLength = 4000; body.spellcheck = false;

        // honeypot (hidden from humans, bots fill it)
        var hp = el('input'); hp.type = 'text'; hp.name = 'website'; hp.tabIndex = -1;
        hp.autocomplete = 'off'; hp.style.position = 'absolute'; hp.style.left = '-9999px'; hp.setAttribute('aria-hidden', 'true');

        var btn = el('button', 'btn btn-primary btn-sm', 'Post reply'); btn.type = 'submit';

        box.appendChild(nick); box.appendChild(body); box.appendChild(hp); box.appendChild(btn);
        box.addEventListener('submit', function (e) {
            e.preventDefault();
            if (!body.value.trim()) { notice('Please write a reply.', 'warning'); return; }
            notice('');
            setBusy(btn, true, 'Posting…');
            api('reply', { body: form({ id: id, nick: nick.value, body: body.value, website: hp.value }) })
                .then(function (res) {
                    setBusy(btn, false);
                    if (res && res.ok) { body.value = ''; showThread(id); }
                    else { notice((res && res.error) || 'Could not post reply.', 'danger'); }
                }).catch(function () { setBusy(btn, false); notice('Network error — try again.', 'danger'); });
        });
        return box;
    }

    /* ---- new-thread form (static, above the list) ------------------------- */
    function wireNewForm() {
        newForm = document.getElementById('cm-new-form');
        if (!newForm) { return; }
        var nick = document.getElementById('cm-new-nick');
        var title = document.getElementById('cm-new-title');
        var body = document.getElementById('cm-new-body');
        var hp = document.getElementById('cm-new-hp');
        var btn = document.getElementById('cm-new-btn');

        newForm.addEventListener('submit', function (e) {
            e.preventDefault();
            if (!title.value.trim()) { notice('Please add a title.', 'warning'); return; }
            if (!body.value.trim()) { notice('Please write a message.', 'warning'); return; }
            notice('');
            setBusy(btn, true, 'Posting…');
            api('new', { body: form({ nick: nick.value, title: title.value, body: body.value, website: hp.value }) })
                .then(function (res) {
                    setBusy(btn, false);
                    if (res && res.ok && res.id) {
                        title.value = ''; body.value = '';
                        location.hash = '#t/' + res.id;
                    } else if (res && res.ok) {
                        title.value = ''; body.value = ''; route();   // honeypot shadow-drop
                    } else {
                        notice((res && res.error) || 'Could not post.', 'danger');
                    }
                }).catch(function () { setBusy(btn, false); notice('Network error — try again.', 'danger'); });
        });
    }

    /* ---- router ----------------------------------------------------------- */
    function route() {
        var h = location.hash || '';
        var m = /^#t\/([a-f0-9]{6,40})$/.exec(h);
        if (m) { showThread(m[1]); window.scrollTo(0, 0); }
        else { showList(); }
    }

    document.addEventListener('DOMContentLoaded', function () {
        root = document.getElementById('community-root');
        if (!root) { return; }
        wireNewForm();
        window.addEventListener('hashchange', route);
        route();
        var refresh = document.getElementById('cm-refresh');
        if (refresh) { refresh.addEventListener('click', function (e) { e.preventDefault(); route(); }); }
    });
})();
