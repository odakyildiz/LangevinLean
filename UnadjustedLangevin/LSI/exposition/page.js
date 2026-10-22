(() => {
  'use strict';

  const mode = document.getElementById('reading-mode');
  const proofToggle = document.getElementById('toggle-proofs');
  const printButton = document.getElementById('print-document');
  const search = document.getElementById('source-search');
  const status = document.getElementById('action-status');
  const proofs = Array.from(document.querySelectorAll('details.lean-proof'));
  const modules = Array.from(document.querySelectorAll('.source-module'));
  const sources = Object.create(null);
  let statusTimer;

  if (status) {
    status.setAttribute('role', 'status');
    status.setAttribute('aria-live', 'polite');
    status.setAttribute('aria-atomic', 'true');
  }

  function announce(message) {
    if (!status) return;
    clearTimeout(statusTimer);
    status.textContent = message;
    statusTimer = setTimeout(() => { status.textContent = ''; }, 7000);
  }

  try {
    const embedded = document.getElementById('lean-sources');
    if (embedded) {
      const parsed = JSON.parse(embedded.textContent);
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) {
        for (const [path, source] of Object.entries(parsed)) {
          if (typeof source === 'string') sources[path] = source;
        }
      }
    }
  } catch (_) {
    announce('Embedded source data could not be read. The displayed proofs remain available.');
  }

  function updateProofToggle() {
    if (!proofToggle) return;
    const allOpen = proofs.length > 0 && proofs.every(proof => proof.open);
    proofToggle.textContent = allOpen ? 'Fold Lean proofs' : 'Open Lean proofs';
    proofToggle.setAttribute('aria-expanded', String(allOpen));
    proofToggle.disabled = proofs.length === 0 || document.body.dataset.mode === 'math';
  }

  function setMode(value, notify = false) {
    const selected = value === 'math' ? 'math' : 'paired';
    document.body.dataset.mode = selected;
    if (mode) mode.value = selected;
    updateProofToggle();
    if (notify) announce(selected === 'math' ? 'Mathematics only.' : 'Mathematics and Lean proofs.');
  }

  setMode(mode ? mode.value : document.body.dataset.mode);
  if (mode) mode.addEventListener('change', () => setMode(mode.value, true));
  if (proofToggle) {
    proofToggle.addEventListener('click', () => {
      const open = !proofs.every(proof => proof.open);
      proofs.forEach(proof => { proof.open = open; });
      updateProofToggle();
      announce(open ? 'All Lean proofs are open.' : 'All Lean proofs are folded.');
    });
  }
  proofs.forEach(proof => proof.addEventListener('toggle', updateProofToggle));
  if (printButton) printButton.addEventListener('click', () => window.print());
  let printProofState = null;
  window.addEventListener('beforeprint', () => {
    if (printProofState) return;
    printProofState = proofs.map(proof => proof.open);
    proofs.forEach(proof => { proof.open = true; });
  });
  window.addEventListener('afterprint', () => {
    if (!printProofState) return;
    proofs.forEach((proof, index) => { proof.open = printProofState[index]; });
    printProofState = null;
    updateProofToggle();
  });

  function filterSources(notify = false) {
    const query = search ? search.value.trim().toLocaleLowerCase() : '';
    let count = 0;
    modules.forEach(module => {
      const path = module.dataset.module || '';
      const matches = path.toLocaleLowerCase().includes(query);
      module.hidden = !matches;
      if (matches) count += 1;
    });
    const countLabel = document.getElementById('source-count');
    if (countLabel) countLabel.textContent = `${count} of ${modules.length} source modules`;
    if (notify) announce(`${count} source ${count === 1 ? 'module matches' : 'modules match'}.`);
  }
  if (search) search.addEventListener('input', () => filterSources(true));
  filterSources();

  function sourceFor(path) {
    return Object.prototype.hasOwnProperty.call(sources, path) ? sources[path] : null;
  }

  function fallbackCopy(text) {
    const active = document.activeElement;
    const selection = window.getSelection();
    const ranges = selection ? Array.from({ length: selection.rangeCount }, (_, i) => selection.getRangeAt(i).cloneRange()) : [];
    const area = document.createElement('textarea');
    area.value = text;
    area.readOnly = true;
    area.setAttribute('aria-label', 'Source code to copy');
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

  async function copySource(path, action) {
    let source = sourceFor(path);
    if (source === null) { announce('This module is not in the embedded source library.'); return; }
    if (action && action.classList.contains('copy-excerpt')) {
      const start = Number(action.dataset.start);
      const end = Number(action.dataset.end);
      if (!Number.isInteger(start) || !Number.isInteger(end) || start < 1 || end < start) return;
      source = source.split(/\r?\n/).slice(start - 1, end).join('\n');
    }
    let copied = false;
    try {
      if (navigator.clipboard && typeof navigator.clipboard.writeText === 'function') {
        try { await navigator.clipboard.writeText(source); copied = true; } catch (_) { /* Local files may need the selection fallback. */ }
      }
      if (!copied) copied = fallbackCopy(source);
    } catch (_) { /* Selection copying may be denied as well. */ }
    if (action) {
      const originalLabel = action.dataset.copyLabel || action.textContent;
      action.dataset.copyLabel = originalLabel;
      clearTimeout(action.copyResetTimer);
      action.textContent = copied ? 'Copied' : 'Copy unavailable';
      action.copyResetTimer = setTimeout(() => { action.textContent = originalLabel; }, 2500);
    }
    announce(copied ? `Copied ${path}.` : 'Copy is unavailable in this browser. Use Save source to get the exact file.');
  }

  function saveSource(path) {
    const source = sourceFor(path);
    if (source === null) { announce('This module is not in the embedded source library.'); return; }
    let url;
    try {
      url = URL.createObjectURL(new Blob([source], { type: 'text/plain;charset=utf-8' }));
      const link = document.createElement('a');
      link.href = url;
      link.download = path.split('/').pop() || 'source.lean';
      document.body.appendChild(link);
      link.click();
      link.remove();
      announce(`Saved ${path}.`);
    } catch (_) {
      announce('The source file could not be saved in this browser.');
    } finally {
      if (url) setTimeout(() => URL.revokeObjectURL(url), 1000);
    }
  }

  function hashTarget(hash) {
    if (!hash || hash === '#') return null;
    try { return document.getElementById(decodeURIComponent(hash.slice(1))); } catch (_) { return null; }
  }

  function lineNumber(line) {
    const explicit = line.dataset.line;
    if (explicit && /^\d+$/.test(explicit)) return Number(explicit);
    const match = line.id.match(/-(\d+)$/);
    if (match) return Number(match[1]);
    const label = line.querySelector('.line-number');
    return label && /^\d+$/.test(label.textContent.trim()) ? Number(label.textContent.trim()) : null;
  }

  function moduleFor(path) {
    return modules.find(module => module.dataset.module === path) || null;
  }

  function clearHighlights() {
    document.querySelectorAll('.source-highlight').forEach(line => line.classList.remove('source-highlight'));
  }

  function reveal(target, focus = true) {
    if (!target) return;
    const sourceModule = target.closest('.source-module');
    if (sourceModule && sourceModule.hidden) {
      if (search) search.value = '';
      filterSources();
    }
    if (target.closest('.lean-proof, .lean-proofs') && document.body.dataset.mode === 'math') setMode('paired');
    let parent = target;
    while (parent) {
      if (parent instanceof HTMLDetailsElement) parent.open = true;
      parent = parent.parentElement;
    }
    updateProofToggle();
    if (focus) {
      if (!target.matches('a, button, input, select, textarea, summary, [tabindex]')) target.setAttribute('tabindex', '-1');
      target.focus({ preventScroll: true });
    }
    target.scrollIntoView({ block: target.classList.contains('line') ? 'center' : 'start', inline: 'nearest', behavior: 'auto' });
  }

  function followHash(focus = true) {
    clearHighlights();
    const target = hashTarget(window.location.hash);
    if (target && target.classList.contains('line')) target.classList.add('source-highlight');
    reveal(target, focus);
  }

  document.addEventListener('click', event => {
    if (!(event.target instanceof Element)) return;
    const action = event.target.closest('button.copy-source, button.save-source');
    if (action) {
      const path = action.dataset.source;
      if (action.classList.contains('copy-source')) void copySource(path, action);
      else saveSource(path);
      return;
    }
    const link = event.target.closest('a[href^="#"]');
    if (!link || event.defaultPrevented || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    const hash = link.getAttribute('href');
    let target = hashTarget(hash);
    const sourceModule = link.dataset.source ? moduleFor(link.dataset.source) : null;
    const start = Number(link.dataset.start);
    const end = Number(link.dataset.end || link.dataset.start);
    if (link.classList.contains('module-link') && sourceModule) {
      if (Number.isInteger(start) && start > 0) {
        target = Array.from(sourceModule.querySelectorAll('.line')).find(line => lineNumber(line) === start) || target || sourceModule;
      } else target = target || sourceModule;
    }
    if (!target) return;
    event.preventDefault();
    clearHighlights();
    if (sourceModule && Number.isInteger(start) && start > 0) {
      sourceModule.querySelectorAll('.line').forEach(line => {
        const n = lineNumber(line);
        if (n !== null && n >= start && n <= (Number.isInteger(end) && end >= start ? end : start)) line.classList.add('source-highlight');
      });
    } else if (target.classList.contains('line')) target.classList.add('source-highlight');
    const nextHash = target.id ? `#${encodeURIComponent(target.id)}` : hash;
    if (window.location.hash !== nextHash) {
      try { window.history.pushState(null, '', nextHash); }
      catch (_) { window.location.hash = nextHash; }
    }
    reveal(target);
  });

  window.addEventListener('hashchange', () => followHash());
  window.addEventListener('popstate', () => followHash());
  if (window.location.hash) requestAnimationFrame(() => followHash(false));
})();
