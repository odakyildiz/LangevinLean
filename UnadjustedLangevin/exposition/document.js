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
  function fallbackCopy(text) {
    const active = document.activeElement;
    const selection = window.getSelection();
    const ranges = selection ? Array.from({ length: selection.rangeCount }, (_, i) => selection.getRangeAt(i).cloneRange()) : [];
    const area = document.createElement('textarea');
    area.value = text;
    area.readOnly = true;
    area.setAttribute('aria-label', 'Lean code to copy');
    Object.assign(area.style, { position: 'fixed', top: '0', left: '0', width: '1px', height: '1px', opacity: '0' });
    document.body.appendChild(area);
    let copied = false;
    try {
      area.focus({ preventScroll: true });
      area.select();
      area.setSelectionRange(0, area.value.length);
      copied = typeof document.execCommand === 'function' && document.execCommand('copy');
    } finally {
      area.remove();
      if (active && typeof active.focus === 'function') active.focus({ preventScroll: true });
      if (selection) {
        selection.removeAllRanges();
        ranges.forEach(range => selection.addRange(range));
      }
    }
    return copied;
  }
  async function copyText(text) {
    if (navigator.clipboard && typeof navigator.clipboard.writeText === 'function') {
      try { await navigator.clipboard.writeText(text); return true; } catch (_) { /* file URLs can deny clipboard access */ }
    }
    return fallbackCopy(text);
  }
  const embeddedSources = JSON.parse(document.getElementById('lean-sources').textContent);
  document.querySelectorAll('pre.note-code').forEach(code => {
    const actions = document.createElement('div');
    actions.className = 'code-label';
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'copy-code';
    button.setAttribute('data-copy-next', '');
    button.textContent = 'Copy Lean';
    actions.appendChild(button);
    code.before(actions);
  });
  document.querySelectorAll('.copy-code').forEach(button => {
    const originalLabel = button.textContent;
    let resetTimer;
    button.addEventListener('click', async () => {
      const code = button.hasAttribute('data-copy-next')
        ? button.parentElement.nextElementSibling
        : document.getElementById(button.dataset.code);
      if (!code) return;
      const lines = [...code.querySelectorAll('.line-text')];
      const text = code.dataset.role === 'module' && Object.prototype.hasOwnProperty.call(embeddedSources, code.dataset.source)
        ? embeddedSources[code.dataset.source]
        : lines.length ? lines.map(line => line.textContent).join('\n') : code.textContent;
      let copied = false;
      try { copied = await copyText(text); } catch (_) { /* Keep a clear failure message if selection copying is unavailable. */ }
      button.textContent = copied ? 'Copied' : 'Copy unavailable';
      announce(copied ? 'Lean code copied.' : 'Copy is unavailable in this browser. Use Save file for the complete source.');
      clearTimeout(resetTimer);
      resetTimer = setTimeout(() => { button.textContent = originalLabel; }, 2500);
    });
  });
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
