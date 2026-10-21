'use strict';
(() => {
  const $ = (selector, scope = document) => scope.querySelector(selector);
  const $$ = (selector, scope = document) => Array.from(scope.querySelectorAll(selector));
  let data;
  try { data = JSON.parse($('#tutorial-data').textContent); } catch (_) { return; }
  const lessons = data.lessons;
  const byLesson = new Map(lessons.map(lesson => [lesson.id, lesson]));
  const sequence = lessons.flatMap(lesson => lesson.steps.map(step => ({...step, lesson: lesson.id})));
  const byStep = new Map(sequence.map(step => [step.id, step]));
  const status = $('#reader-status');
  let current = null;
  let currentLesson = null;
  let lastReading = null;
  let saved = null;
  try { saved = JSON.parse(localStorage.getItem('convexity-in-lean-v1')); } catch (_) {}

  function node(tag, className, text) {
    const element = document.createElement(tag);
    if (className) element.className = className;
    if (text !== undefined) element.textContent = text;
    return element;
  }
  function renderMath(scope = document) {
    $$('[data-tex]', scope).forEach(element => {
      if (element.dataset.rendered || !window.katex) return;
      try {
        katex.render(element.dataset.tex, element, {displayMode: element.dataset.display === 'true', throwOnError: true, strict: 'error'});
        element.dataset.rendered = 'true';
      } catch (_) { element.classList.add('math-error'); }
    });
  }
  function annotate(parent, value) {
    if (Array.isArray(value)) { value.forEach(item => annotate(parent, item)); return; }
    // Only repository-owned annotation text is rendered, with a small HTML
    // vocabulary and explicit TeX delimiters; no arbitrary attributes survive.
    let text = String(value || '').replace(/`([^`]+)`/g, (_, code) => '<code>' + code.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;') + '</code>');
    const formulas = [];
    text = text.replace(/\\\[([\s\S]*?)\\\]|\\\(([\s\S]*?)\\\)/g, (_, display, inline) => {
      const index = formulas.push({tex: display || inline, display: display !== undefined}) - 1;
      return '<span data-formula="' + index + '"></span>';
    });
    const template = document.createElement('template');
    template.innerHTML = text;
    const allowed = new Set(['P', 'EM', 'STRONG', 'CODE', 'BR', 'UL', 'OL', 'LI', 'SPAN']);
    function clean(source) {
      if (source.nodeType === Node.TEXT_NODE) return document.createTextNode(source.textContent);
      if (source.nodeType !== Node.ELEMENT_NODE) return document.createTextNode('');
      if (source.hasAttribute('data-formula')) {
        const formula = formulas[Number(source.dataset.formula)];
        const result = node(formula.display ? 'div' : 'span', 'math');
        result.dataset.tex = formula.tex;
        result.dataset.display = String(formula.display);
        return result;
      }
      if (['SCRIPT', 'STYLE', 'IFRAME'].includes(source.tagName)) return document.createTextNode('');
      const result = allowed.has(source.tagName) ? document.createElement(source.tagName.toLowerCase()) : document.createDocumentFragment();
      Array.from(source.childNodes).forEach(child => result.append(clean(child)));
      return result;
    }
    Array.from(template.content.childNodes).forEach(child => parent.append(clean(child)));
  }
  function clearMarks() {
    $$('.syntax-mark').forEach(mark => { const parent = mark.parentNode; mark.replaceWith(...mark.childNodes); parent.normalize(); });
  }
  function highlightToken(card, token, range = null) {
    clearMarks();
    if (!token) return;
    $$('.code-line', card).filter(line => range ? Number(line.dataset.line) >= range.start && Number(line.dataset.line) <= range.end : line.classList.contains('linked')).forEach(line => {
      const walker = document.createTreeWalker(line, NodeFilter.SHOW_TEXT, {
        acceptNode: entry => entry.parentElement.closest('.line-number') ? NodeFilter.FILTER_REJECT : NodeFilter.FILTER_ACCEPT
      });
      const segments = [];
      let text = '';
      while (walker.nextNode()) {
        const entry = walker.currentNode;
        segments.push({node: entry, start: text.length, end: text.length + entry.textContent.length});
        text += entry.textContent;
      }
      const matches = [];
      let offset = 0;
      while ((offset = text.indexOf(token, offset)) >= 0) {
        const identifier = /^[A-Za-z_][\w']*$/.test(token);
        if (!identifier || (!/[\w']/u.test(text[offset - 1] || '') && !/[\w']/u.test(text[offset + token.length] || ''))) matches.push(offset);
        offset += token.length;
      }
      matches.reverse().forEach(start => {
        const first = segments.find(entry => start >= entry.start && start < entry.end);
        const last = segments.find(entry => start + token.length > entry.start && start + token.length <= entry.end);
        if (!first || !last) return;
        const range = document.createRange();
        range.setStart(first.node, start - first.start);
        range.setEnd(last.node, start + token.length - last.start);
        const mark = node('mark', 'syntax-mark');
        mark.append(range.extractContents());
        range.insertNode(mark);
      });
    });
  }
  function stateText(value) {
    if (typeof value === 'string') return value || 'No goals remain.';
    if (value && typeof value.raw === 'string') return value.raw || 'No goals remain.';
    return null;
  }
  function explanation(section, step) {
    const panel = $('.code-explanation', section);
    panel.replaceChildren(node('h4', '', (step.kind === 'declaration' ? 'Reading this definition' : 'Reading these commands') + ' · lines ' + step.start + '–' + step.end));
    if (step.codeNotes?.length) {
      const list = node('ul');
      step.codeNotes.forEach(note => { const entry = node('li'); annotate(entry, note); list.append(entry); });
      panel.append(list);
    }
    if (step.tokens?.length) {
      panel.append(node('p', 'syntax-label', 'Select a code piece to inspect its meaning.'));
      const chips = node('div', 'syntax-tokens');
      chips.setAttribute('role', 'group');
      chips.setAttribute('aria-label', 'Explain the code pieces in this step');
      const description = node('div', 'token-explanation');
      description.setAttribute('aria-live', 'polite');
      step.tokens.forEach((entry, index) => {
        const button = node('button', '', entry.token);
        button.type = 'button';
        button.setAttribute('aria-pressed', String(index === 0));
        button.addEventListener('click', () => {
          $$('button', chips).forEach(control => control.setAttribute('aria-pressed', String(control === button)));
          description.replaceChildren();
          annotate(description, entry.explanation || entry.description);
          renderMath(description);
          highlightToken($('.source-card', section), entry.token);
        });
        if (index === 0) annotate(description, entry.explanation || entry.description);
        chips.append(button);
      });
      panel.append(chips, description);
    }
    if (step.context?.length) {
      const details = node('details', 'context-explanations');
      details.append(node('summary', '', 'Names used in this step'));
      const list = node('dl');
      step.context.forEach(entry => {
        list.append(node('dt', '', entry.name));
        const meaning = node('dd');
        annotate(meaning, entry.meaning);
        list.append(meaning);
      });
      details.append(list);
      panel.append(details);
    }
    renderMath(panel);
    const before = $('.goal-before', section);
    const after = $('.goal-after', section);
    const captured = step.verifiedState;
    const declaring = step.kind === 'declaration';
    $('.goal-panel', section).hidden = declaring;
    before.textContent = declaring ? 'A definition introduces a property. There is no tactic proof goal in this declaration.' :
      stateText(captured?.before) || 'A verified proof-state capture is not available for this step.';
    after.textContent = declaring ? 'IsConvex is now a name for the displayed proposition. The first theorem begins in the next lesson.' :
      stateText(captured?.after) || 'A verified proof-state capture is not available for this step.';
    before.classList.toggle('no-goals', declaring || captured?.before?.raw === '');
    after.classList.toggle('no-goals', declaring || captured?.after?.raw === '');
  }
  function select(id, {hash = true, focus = false} = {}) {
    const step = byStep.get(id);
    if (!step) return;
    current = id;
    currentLesson = step.lesson;
    lastReading = id;
    $('#source-browser').hidden = true;
    $$('.lesson').forEach(section => { section.hidden = section.dataset.lesson !== step.lesson; });
    const section = document.getElementById('lesson-' + step.lesson);
    $$('.math-step', section).forEach(element => element.classList.toggle('active', element.dataset.step === id));
    $$('.step-choice', section).forEach(button => button.setAttribute('aria-pressed', String(button.dataset.step === id)));
    $$('.lesson-link').forEach(link => {
      const active = link.dataset.lesson === step.lesson;
      link.classList.toggle('active', active);
      if (active) link.setAttribute('aria-current', 'step'); else link.removeAttribute('aria-current');
    });
    clearMarks();
    const lines = $$('.code-line', section);
    lines.forEach(line => {
      const number = Number(line.dataset.line);
      line.classList.toggle('linked', number >= step.start && number <= step.end);
      line.classList.toggle('range-start', number === step.start);
      line.classList.toggle('range-end', number === step.end);
    });
    explanation(section, step);
    const index = sequence.findIndex(entry => entry.id === id);
    $('.step-prev', section).disabled = index === 0;
    $('.step-next', section).disabled = index === sequence.length - 1;
    const local = byLesson.get(step.lesson).steps.findIndex(entry => entry.id === id);
    $('.step-position', section).textContent = 'Step ' + (local + 1) + ' of ' + byLesson.get(step.lesson).steps.length;
    const next = sequence[index + 1];
    $('.step-next', section).textContent = next && next.lesson !== step.lesson ? 'Next proof →' : index === sequence.length - 1 ? 'End of tutorial' : 'Next →';
    if (hash) history.pushState({step: id}, '', '#step-' + encodeURIComponent(id));
    try { localStorage.setItem('convexity-in-lean-v1', JSON.stringify({step: id})); } catch (_) {}
    status.textContent = byLesson.get(step.lesson).title + ': ' + step.title + '.';
    if (focus) {
      const target = $('.step-choice[aria-pressed=true]', section);
      target.focus({preventScroll: true});
      section.scrollIntoView({behavior: 'auto', block: 'start'});
    }
  }
  function openFiles(file, line) {
    lastReading = current || lastReading;
    $$('.lesson').forEach(section => { section.hidden = true; });
    $('#source-browser').hidden = false;
    const target = file && $$('.file-source').find(section => section.dataset.file === file);
    const codeLine = target && $$('.code-line', target).find(row => Number(row.dataset.line) === Number(line));
    const anchor = codeLine || $('#source-browser');
    history.pushState({source: file, line}, '', '#' + anchor.id);
    anchor.scrollIntoView({behavior: 'auto', block: codeLine ? 'center' : 'start'});
    $('#return-to-proof').focus({preventScroll: true});
  }
  $$('.lesson-link').forEach(link => link.addEventListener('click', event => {
    if (event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    event.preventDefault();
    select(byLesson.get(link.dataset.lesson).steps[0].id, {focus: true});
  }));
  $$('.step-choice').forEach(button => button.addEventListener('click', () => select(button.dataset.step)));
  $$('.lesson').forEach(section => {
    const lesson = byLesson.get(section.dataset.lesson);
    const statementPanel = $('.statement-token-panel', section);
    if (statementPanel) {
      const controls = node('div', 'syntax-tokens');
      const description = node('div', 'token-explanation', 'Select a piece of the statement to read its meaning.');
      lesson.statementTokens.forEach(entry => {
        const button = node('button', '', entry.token);
        button.type = 'button';
        button.setAttribute('aria-pressed', 'false');
        button.addEventListener('click', () => {
          $$('button', controls).forEach(control => control.setAttribute('aria-pressed', String(control === button)));
          description.replaceChildren();
          annotate(description, entry.explanation);
          renderMath(description);
          highlightToken($('.source-card', section), entry.token, lesson.declaration);
        });
        controls.append(button);
      });
      statementPanel.append(controls, description);
    }
    $$('.code-line', section).forEach(line => {
      const number = Number(line.dataset.line);
      const candidates = lesson.steps.filter(step => number >= step.start && number <= step.end);
      const candidate = candidates.sort((a, b) => (a.end - a.start) - (b.end - b.start))[0];
      if (!candidate) return;
      line.dataset.linkedStep = candidate.id;
      line.addEventListener('click', () => {
        if (window.getSelection()?.toString()) return;
        select(candidate.id);
      });
    });
    $('.step-prev', section).addEventListener('click', () => select(sequence[sequence.findIndex(step => step.id === current) - 1]?.id, {focus: true}));
    $('.step-next', section).addEventListener('click', () => select(sequence[sequence.findIndex(step => step.id === current) + 1]?.id, {focus: true}));
  });
  $$('.copy-source').forEach(button => button.addEventListener('click', async () => {
    const source = $$('.code-line', button.closest('.source-card')).map(line => {
      const clone = line.cloneNode(true);
      $('.line-number', clone)?.remove();
      return clone.textContent;
    }).join('\n');
    try { await navigator.clipboard.writeText(source); button.textContent = 'Copied'; }
    catch (_) { status.textContent = 'Select the source text to copy it.'; }
  }));
  $$('.open-source').forEach(link => link.addEventListener('click', event => {
    event.preventDefault();
    openFiles(link.dataset.file, link.dataset.line);
  }));
  $('#show-files').addEventListener('click', () => openFiles());
  $('#return-to-proof').addEventListener('click', () => select(lastReading || sequence[0].id, {focus: true}));
  $('#show-notation').addEventListener('click', event => {
    const guide = $('#notation-guide');
    guide.hidden = !guide.hidden;
    event.currentTarget.setAttribute('aria-expanded', String(!guide.hidden));
    if (!guide.hidden) guide.scrollIntoView({behavior: 'auto', block: 'start'});
  });
  if (saved && byStep.has(saved.step)) {
    const resume = $('#resume-reading');
    resume.hidden = false;
    resume.textContent = 'Resume: ' + byLesson.get(byStep.get(saved.step).lesson).title;
    resume.addEventListener('click', () => select(saved.step, {focus: true}));
  }
  function route() {
    let hash = '';
    try { hash = decodeURIComponent(location.hash.slice(1)); } catch (_) {}
    if (hash.startsWith('step-') && byStep.has(hash.slice(5))) select(hash.slice(5), {hash: false});
    else if (hash.startsWith('lesson-') && byLesson.has(hash.slice(7))) select(byLesson.get(hash.slice(7)).steps[0].id, {hash: false});
    else if (hash.startsWith('source-') || hash === 'source-browser') {
      $$('.lesson').forEach(section => { section.hidden = true; });
      $('#source-browser').hidden = false;
      requestAnimationFrame(() => document.getElementById(hash)?.scrollIntoView({block: 'center'}));
    } else select(sequence[0].id, {hash: false});
  }
  renderMath();
  document.body.classList.add('enhanced');
  route();
  window.addEventListener('hashchange', route);
  window.addEventListener('popstate', route);
})();
