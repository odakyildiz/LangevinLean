/* Shared by the current pages and the self-contained exposition archives. */
(() => {
  'use strict';
  const root = document.documentElement;
  const key = 'langevin-theme';
  const valid = value => ['system', 'light', 'dark'].includes(value);
  let preference = 'system';
  let media;
  try { media = window.matchMedia('(prefers-color-scheme: dark)'); } catch (_) {}
  try {
    const stored = window.localStorage.getItem(key);
    if (valid(stored)) preference = stored;
  } catch (_) {}

  const apply = () => {
    const resolved = preference === 'system' ? (media && media.matches ? 'dark' : 'light') : preference;
    root.dataset.theme = resolved;
    root.dataset.themePreference = preference;
    document.querySelectorAll('[data-theme-control]').forEach(control => {
      control.value = preference;
    });
  };
  // Run in the head, before the page is painted.
  apply();
  const bind = () => {
    document.querySelectorAll('[data-theme-control]').forEach(control => {
      control.addEventListener('change', () => {
        if (!valid(control.value)) return;
        preference = control.value;
        try { window.localStorage.setItem(key, preference); } catch (_) {}
        apply();
      });
    });
    apply();
  };
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', bind, { once: true });
  else bind();
  const onSystemChange = () => { if (preference === 'system') apply(); };
  if (media && media.addEventListener) media.addEventListener('change', onSystemChange);
  else if (media && media.addListener) media.addListener(onSystemChange);
  window.addEventListener('storage', event => {
    if (event.key !== key && event.key !== null) return;
    preference = valid(event.newValue) ? event.newValue : 'system';
    apply();
  });
})();
