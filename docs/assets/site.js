'use strict';
(() => {
  const select = document.querySelector('#reading-mode');
  function mode(value) {
    document.body.classList.remove('reading-math', 'reading-lean');
    if (value !== 'paired') document.body.classList.add('reading-' + value);
    if (select) select.value = value;
  }
  try { mode(localStorage.getItem('langevin-reading') || 'paired'); } catch (_) {}
  select?.addEventListener('change', () => {
    mode(select.value);
    try { localStorage.setItem('langevin-reading', select.value); } catch (_) {}
  });
  const search = document.querySelector('#module-search');
  function filter() {
    const query = search.value.toLowerCase().trim();
    let count = 0;
    document.querySelectorAll('.module-card').forEach(card => {
      card.hidden = !card.textContent.toLowerCase().includes(query);
      if (!card.hidden) count++;
    });
    document.querySelectorAll('.module-group').forEach(group => {
      group.hidden = !group.querySelector('.module-card:not([hidden])');
    });
    document.querySelector('#module-count').textContent = `${count} modules`;
  }
  search?.addEventListener('input', filter);
  if (search) filter();
  let statusTimer;
  function fallbackCopy(value) {
    const previous = document.activeElement;
    const selection = window.getSelection();
    const ranges = selection ? Array.from({ length: selection.rangeCount }, (_, i) => selection.getRangeAt(i).cloneRange()) : [];
    const input = document.createElement('textarea');
    input.value = value;
    input.readOnly = true;
    input.setAttribute('aria-label', 'Lean source to copy');
    input.style.cssText = 'position:fixed;top:0;left:0;width:1px;height:1px;opacity:0;';
    document.body.append(input);
    try {
      input.focus({ preventScroll: true });
      input.select();
      input.setSelectionRange(0, value.length);
      return typeof document.execCommand === 'function' && document.execCommand('copy');
    } finally {
      input.remove();
      previous?.focus({ preventScroll: true });
      if (selection) {
        selection.removeAllRanges();
        ranges.forEach(range => selection.addRange(range));
      }
    }
  }
  async function copyText(value) {
    if (navigator.clipboard && typeof navigator.clipboard.writeText === 'function') {
      try { await navigator.clipboard.writeText(value); return true; } catch (_) { /* Local files may deny clipboard access. */ }
    }
    return fallbackCopy(value);
  }
  document.querySelectorAll('[data-copy], [data-copy-lean]').forEach(button => {
    button.addEventListener('click', async () => {
      const value = button.hasAttribute('data-copy-lean')
        ? Array.from(button.closest('.code-wrap').querySelectorAll('.line-text'), line => line.textContent).join('\n')
        : document.getElementById(button.dataset.copy).textContent;
      const status = document.querySelector('#action-status');
      let copied = false;
      try {
        copied = await copyText(value);
      } catch (_) { /* Some browsers block both clipboard methods. */ }
      const label = button.dataset.copyLabel || button.textContent;
      button.dataset.copyLabel = label;
      clearTimeout(button.copyResetTimer);
      button.textContent = copied ? 'Copied' : 'Copy unavailable';
      button.copyResetTimer = setTimeout(() => { button.textContent = label; }, 2500);
      if (status) {
        status.textContent = copied ? 'Copied plain text.' : 'Copy is unavailable in this browser. Open the linked source file to select its text.';
        clearTimeout(statusTimer); statusTimer = setTimeout(() => { status.textContent = ''; }, 4000);
      }
    });
  });
  // An identifier quoted in the mathematical or Lean explanation highlights
  // the exact source line it refers to while it is hovered or focused.
  document.querySelectorAll('a.proof-source-ref[href^="#"]').forEach(link => {
    const line = document.getElementById(decodeURIComponent(link.getAttribute('href').slice(1)));
    if (!line) return;
    const on = () => line.classList.add('source-highlight');
    const off = () => line.classList.remove('source-highlight');
    link.addEventListener('mouseenter', on);
    link.addEventListener('mouseleave', off);
    link.addEventListener('focus', on);
    link.addEventListener('blur', off);
  });
  document.querySelector('#print-page')?.addEventListener('click', () => window.print());
  if (location.hash) {
    const target = document.getElementById(decodeURIComponent(location.hash.slice(1)));
    target?.closest('details')?.setAttribute('open', '');
    const legacy = document.querySelector('#legacy-destination');
    if (!target && legacy) location.replace(legacy.dataset.url + location.hash);
  }
})();
