/*
 * Page integrity helper.
 *
 * Historically this script computed a SHA-256 of the page and wrote it into
 * the address bar as a "#SHA256-..." fragment. That fragment is no longer
 * wanted anywhere on the site, so this script now only cleans it up: if the
 * URL still carries a legacy "#SHA256-..." fragment it is stripped on load.
 * It never adds the fragment again, and any real "#section" anchor is left
 * untouched.
 */
(function () {
    'use strict';
    try {
        if (/^#SHA256-/i.test(location.hash) && window.history && history.replaceState) {
            history.replaceState(history.state, document.title,
                location.pathname + location.search);
        }
    } catch (e) {}
}());
