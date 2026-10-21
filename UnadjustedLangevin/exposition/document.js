(() => {
  'use strict';
  const root = document.documentElement;
  const mode = document.getElementById('reading-mode');
  const fullButton = document.getElementById('toggle-full');
  const notesButton = document.getElementById('toggle-notes');
  const progress = document.getElementById('reading-progress');
  const current = document.getElementById('current-section');
  const status = document.getElementById('status');
  let statusTimer;
  function announce(message) {
    status.textContent = message;
    clearTimeout(statusTimer);
    statusTimer = setTimeout(() => { status.textContent = ''; }, 2500);
  }
  mode.addEventListener('change', () => {
    root.classList.toggle('math-only', mode.value === 'math');
    fullButton.disabled = mode.value === 'math';
    notesButton.disabled = mode.value === 'math';
  });
  function updateNotesLabel() {
    const allOpen = [...document.querySelectorAll('.lean-note')].every(item => item.open);
    notesButton.textContent = allOpen ? 'Close Lean notes' : 'Open Lean notes';
    notesButton.setAttribute('aria-expanded', String(allOpen));
  }
  notesButton.addEventListener('click', () => {
    const all = [...document.querySelectorAll('.lean-note')];
    const open = !all.every(item => item.open);
    all.forEach(item => { item.open = open; });
    updateNotesLabel();
  });
  document.querySelectorAll('.lean-note').forEach(item => item.addEventListener('toggle', updateNotesLabel));
  function updateFullLabel() {
    const allOpen = [...document.querySelectorAll('.full-proof')].every(item => item.open);
    fullButton.textContent = allOpen ? 'Fold full proofs' : 'Unfold full proofs';
    fullButton.setAttribute('aria-expanded', String(allOpen));
  }
  fullButton.addEventListener('click', () => {
    const all = [...document.querySelectorAll('.full-proof')];
    const open = !all.every(item => item.open);
    all.forEach(item => { item.open = open; });
    updateFullLabel();
  });
  document.querySelectorAll('.full-proof').forEach(item => item.addEventListener('toggle', updateFullLabel));
  document.getElementById('print-document').addEventListener('click', () => window.print());
  async function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      try { await navigator.clipboard.writeText(text); return true; } catch (_) { /* file URLs can deny clipboard access */ }
    }
    const area = document.createElement('textarea');
    area.value = text;
    area.style.cssText = 'position:fixed;left:-10000px;top:0';
    document.body.appendChild(area);
    area.select();
    const copied = document.execCommand('copy');
    area.remove();
    return copied;
  }
  document.querySelectorAll('.copy-code').forEach(button => {
    button.addEventListener('click', async () => {
      const code = document.getElementById(button.dataset.code);
      const text = [...code.querySelectorAll('.line-text')].map(line => line.textContent).join('\n');
      announce(await copyText(text) ? 'Lean code copied.' : 'Select the Lean text to copy it.');
    });
  });
  const embeddedSources = JSON.parse(document.getElementById('lean-sources').textContent);
  document.querySelectorAll('[data-download]').forEach(button => {
    button.addEventListener('click', () => {
      const path = button.dataset.download;
      const blob = new Blob([embeddedSources[path]], { type: 'text/plain;charset=utf-8' });
      const url = URL.createObjectURL(blob);
      const anchor = document.createElement('a');
      anchor.href = url;
      anchor.download = path.split('/').pop();
      anchor.click();
      setTimeout(() => URL.revokeObjectURL(url), 1000);
    });
  });
  function showHash() {
    document.querySelectorAll('.selected').forEach(item => item.classList.remove('selected'));
    const id = decodeURIComponent(location.hash.slice(1));
    const target = document.getElementById(id);
    if (!target) return;
    if (target.tagName === 'DETAILS') target.open = true;
    let parent = target.parentElement;
    while (parent) {
      if (parent.tagName === 'DETAILS') parent.open = true;
      parent = parent.parentElement;
    }
    if (target.classList.contains('proof-pair')) target.classList.add('selected');
    requestAnimationFrame(() => target.scrollIntoView({ block: 'start', behavior: 'instant' }));
  }
  window.addEventListener('hashchange', showHash);
  if (location.hash) showHash();
  let printState = [];
  window.addEventListener('beforeprint', () => {
    printState = [...document.querySelectorAll('.full-proof')].map(item => [item, item.open]);
    printState.forEach(([item]) => { item.open = true; });
  });
  window.addEventListener('afterprint', () => {
    printState.forEach(([item, open]) => { item.open = open; });
  });
  const chapters = [...document.querySelectorAll('.chapter')];
  let scheduled = false;
  function updateReading() {
    const max = document.documentElement.scrollHeight - window.innerHeight;
    progress.style.width = `${max > 0 ? Math.min(100, Math.max(0, scrollY / max * 100)) : 0}%`;
    let chapter;
    for (const item of chapters) {
      if (item.getBoundingClientRect().top <= 150) chapter = item;
      else break;
    }
    current.textContent = chapter ? `§ ${chapter.dataset.number} · ${chapter.dataset.title}` : 'A sequential proof';
    scheduled = false;
  }
  window.addEventListener('scroll', () => {
    if (!scheduled) { scheduled = true; requestAnimationFrame(updateReading); }
  }, { passive: true });
  window.addEventListener('resize', updateReading);
  updateReading();
  updateFullLabel();
  updateNotesLabel();
})();
