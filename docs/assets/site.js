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
  document.querySelectorAll('[data-copy]').forEach(button => {
    button.addEventListener('click', async () => {
      const value = document.getElementById(button.dataset.copy).textContent;
      const status = document.querySelector('#action-status');
      try {
        if (navigator.clipboard && window.isSecureContext) await navigator.clipboard.writeText(value);
        else {
          const input = document.createElement('textarea');
          input.value = value; document.body.append(input); input.select();
          const copied = document.execCommand('copy'); input.remove();
          if (!copied) throw Error('copy unavailable');
        }
        status.textContent = 'Copied.';
      } catch (_) { status.textContent = 'Select the command text to copy it.'; }
      clearTimeout(statusTimer); statusTimer = setTimeout(() => { status.textContent = ''; }, 3000);
    });
  });
  document.querySelector('#print-page')?.addEventListener('click', () => window.print());
  if (location.hash) {
    const target = document.getElementById(decodeURIComponent(location.hash.slice(1)));
    target?.closest('details')?.setAttribute('open', '');
    const legacy = document.querySelector('#legacy-destination');
    if (!target && legacy) location.replace(legacy.dataset.url + location.hash);
  }
})();
