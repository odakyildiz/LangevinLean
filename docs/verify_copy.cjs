#!/usr/bin/env node
'use strict';
// Optional local browser regression check. Requires installed Playwright and Chrome.
// NODE_PATH=/path/to/node_modules node docs/verify_copy.cjs
// A temporary copy can use REPO_ROOT=/path/to/LangevinLean.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const http = require('node:http');
const path = require('node:path');
const {pathToFileURL} = require('node:url');
const {chromium} = require('playwright');
const REPO = path.resolve(process.env.REPO_ROOT || path.join(__dirname, '..'));
const chrome = process.env.CHROME_PATH || [
  '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
  '/usr/bin/google-chrome', '/usr/bin/google-chrome-stable', '/usr/bin/chromium',
].find(file => fs.existsSync(file));
assert(chrome, 'Set CHROME_PATH to an installed Chrome/Chromium executable.');
assert(fs.existsSync(path.join(REPO, 'lean-toolchain')), 'Set REPO_ROOT to the repository root.');
let count = 0;
let modernPageCount = 0;
let modernBlockCount = 0;
function checkModernCoverage() {
  const pages = ['index.html', 'UnadjustedLangevin/exposition/index.html',
    'UnadjustedLangevin/LSI/exposition/index.html', 'IPLA/exposition/index.html',
    'IPLA/LSI/exposition/index.html', 'ProximalLangevin/exposition/index.html'];
  function visit(directory) {
    for (const entry of fs.readdirSync(directory, {withFileTypes: true})) {
      const file = path.join(directory, entry.name);
      if (entry.isDirectory()) visit(file);
      else if (entry.name.endsWith('.html')) pages.push(path.relative(REPO, file));
    }
  }
  visit(path.join(REPO, 'docs/modules'));
  for (const page of pages) {
    const html = fs.readFileSync(path.join(REPO, page), 'utf8');
    const blocks = (html.match(/<pre class="lean-code"/g) || []).length;
    const wrappers = (html.match(/<div class="code-wrap"/g) || []).length;
    const buttons = (html.match(/<button\b[^>]*\bdata-copy-lean(?:\s|>)/g) || []).length;
    assert.equal(wrappers, blocks, page + ': every Lean block has a wrapper');
    assert.equal(buttons, blocks, page + ': every Lean block has a Copy Lean button');
    modernBlockCount += blocks;
  }
  modernPageCount = pages.length;
}
const errors = [];
function sourceSlice(file, start, end) {
  return fs.readFileSync(path.join(REPO, file), 'utf8').split(/\r?\n/).slice(start - 1, end).join('\n');
}
function embeddedScript() {
  window.__copyMode = 'success';
  window.__copyCaptured = [];
  window.__copyAttempts = [];
  Object.defineProperty(navigator, 'clipboard', {configurable: true, value: {
    async writeText(value) {
      window.__copyAttempts.push({method: 'clipboard', value});
      if (window.__copyMode !== 'success') throw new DOMException('Test clipboard denial', 'NotAllowedError');
      window.__copyCaptured.push({method: 'clipboard', value});
    },
  }});
  document.execCommand = command => {
    if (command !== 'copy') return false;
    const active = document.activeElement;
    const value = active instanceof HTMLTextAreaElement ? active.value : null;
    const attempt = {method: 'selection', value, textarea: active instanceof HTMLTextAreaElement,
      modal: !!active?.closest('dialog[open]')};
    window.__copyAttempts.push(attempt);
    if (window.__copyMode === 'blocked') return false;
    window.__copyCaptured.push(attempt);
    return true;
  };
}
async function reveal(button) {
  await button.evaluate(element => {
    for (let parent = element.parentElement; parent; parent = parent.parentElement) {
      if (parent instanceof HTMLDetailsElement) parent.open = true;
    }
  });
}
async function checkCopy(page, button, expected, description, mode = 'success', selectionSelector = null) {
  const handle = await button.elementHandle();
  await reveal(handle);
  await page.evaluate(mode => {
    window.__copyMode = mode;
    window.__copyCaptured = [];
    window.__copyAttempts = [];
  }, mode);
  const beforeSelection = await handle.evaluate((element, selector) => {
    element.focus({preventScroll: true});
    const code = selector ? document.querySelector(selector) :
      element.closest('.code-wrap, .archive-code, .lean-proof, details')?.querySelector('.line-text, pre code, pre');
    const selection = window.getSelection();
    if (selection && code) {
      const range = document.createRange();
      range.selectNodeContents(code);
      selection.removeAllRanges();
      selection.addRange(range);
    }
    const text = selection ? selection.toString() : '';
    element.click();
    return text;
  }, selectionSelector);
  try {
    await page.waitForFunction(({button, blocked}) => blocked
      ? /unavailable|failed/i.test(button.textContent) : /copied/i.test(button.textContent),
      {button: handle, blocked: mode === 'blocked'});
  } catch (error) {
    throw new Error(description + ': ' + error.message + '\n' + JSON.stringify(await handle.evaluate(button => ({
      button: button.outerHTML, next: button.parentElement.nextElementSibling?.outerHTML.slice(0, 200),
      attempts: window.__copyAttempts, captured: window.__copyCaptured,
    }))) + '\nBrowser errors: ' + JSON.stringify(errors));
  }
  const state = await handle.evaluate(element => ({
    captured: window.__copyCaptured, attempts: window.__copyAttempts,
    focused: document.activeElement === element,
    selection: window.getSelection()?.toString() || '',
  }));
  if (mode === 'blocked') {
    assert.equal(state.captured.length, 0, description + ': must not claim clipboard success');
    assert(state.attempts.some(attempt => attempt.method === 'selection'), description + ': fallback must be tried');
  } else {
    assert.equal(state.captured.length, 1, description + ': one successful copy');
    assert.equal(state.captured[0].value, expected, description + ': exact Unicode, spacing, and newlines');
    assert.equal(state.captured[0].method, mode === 'success' ? 'clipboard' : 'selection');
    if (mode !== 'success') assert(state.captured[0].textarea, description + ': fallback uses selected textarea');
  }
  assert(state.focused, description + ': focus restored to button');
  assert.equal(state.selection, beforeSelection, description + ': previous selection restored');
  count++;
}
async function both(page, button, expected, description, selectionSelector) {
  await checkCopy(page, button, expected, description + ' Clipboard API', 'success', selectionSelector);
  await checkCopy(page, button, expected, description + ' rejected API fallback', 'reject', selectionSelector);
}
async function modern(page, url, blocked = false) {
  await page.goto(url, {waitUntil: 'domcontentloaded'});
  await page.waitForSelector('.code-wrap [data-copy-lean]', {state: 'attached'});
  const coverage = await page.locator('.code-wrap').evaluateAll(wrappers => wrappers.filter(wrapper => wrapper.querySelector('pre.lean-code')).map(wrapper => wrapper.querySelectorAll('[data-copy-lean]').length));
  assert(coverage.length > 0 && coverage.every(n => n === 1), 'Every modern Lean block has exactly one Copy Lean button');
  assert.equal(await page.locator('pre.lean-code').count(), coverage.length, 'Every modern Lean block is inside its code wrapper');
  const candidates = page.locator('.code-wrap').filter({has: page.locator('pre.lean-code')});
  const index = await candidates.evaluateAll(wrappers => wrappers.findIndex(wrapper => {
    const text = [...wrapper.querySelectorAll('.line-text')].map(line => line.textContent).join('\n');
    return text.includes('\n') && /[θℝ∀∈≤]/u.test(text);
  }));
  assert(index >= 0, 'Modern example contains multiline Unicode Lean');
  const wrapper = candidates.nth(index);
  const info = await wrapper.locator('pre.lean-code').evaluate(pre => ({
    file: pre.dataset.source, start: Number(pre.dataset.start), end: Number(pre.dataset.end),
    text: [...pre.querySelectorAll('.line-text')].map(line => line.textContent).join('\n'),
  }));
  const expected = sourceSlice(info.file, info.start, info.end);
  assert.equal(info.text, expected, 'Rendered example matches the original Lean file slice');
  assert(/^\s+\S/mu.test(expected), 'Example includes meaningful indentation');
  const button = wrapper.locator('[data-copy-lean]');
  await both(page, button, expected, url.startsWith('file:') ? 'offline modern Lean' : 'modern Lean');
  if (blocked) await checkCopy(page, button, expected, 'modern blocked clipboard', 'blocked');
  const module = page.locator('.code-wrap').filter({has: page.locator('pre.lean-code[data-role="module"]')}).first();
  const moduleInfo = await module.locator('pre.lean-code').evaluate(pre => ({
    file: pre.dataset.source, start: Number(pre.dataset.start), end: Number(pre.dataset.end),
    text: [...pre.querySelectorAll('.line-text')].map(line => line.textContent).join('\n'),
  }));
  const moduleExpected = sourceSlice(moduleInfo.file, moduleInfo.start, moduleInfo.end);
  assert.equal(moduleInfo.text, moduleExpected, 'Displayed complete module matches original source without its undisplayed final newline');
  await both(page, module.locator('[data-copy-lean]'), moduleExpected, 'modern complete module');
}
async function commands(page, url) {
  await page.goto(url, {waitUntil: 'domcontentloaded'});
  const statement = page.locator('.code-wrap').filter({has: page.locator('pre.lean-code[data-role="statement"]')}).first();
  const info = await statement.locator('pre.lean-code').evaluate(pre => ({
    file: pre.dataset.source, start: Number(pre.dataset.start), end: Number(pre.dataset.end),
    text: [...pre.querySelectorAll('.line-text')].map(line => line.textContent).join('\n'),
  }));
  // declaration_header intentionally ends at the statement, before ':= by'.
  const lines = sourceSlice(info.file, info.start, info.end).split('\n');
  lines[lines.length - 1] = lines.at(-1).split(':=', 1)[0].trimEnd();
  const expectedStatement = lines.join('\n');
  assert.equal(info.text, expectedStatement, 'Overview header is the original Lean statement prefix');
  assert(!expectedStatement.endsWith(':= by'), 'The statement copy excludes the following proof');
  await both(page, statement.locator('[data-copy-lean]'), expectedStatement, 'modern standalone statement header');
  const commandButtons = page.locator('[data-copy]');
  assert(await commandButtons.count() >= 2, 'Overview exposes both context and compile command controls');
  for (const [button, description] of [[commandButtons.first(), 'modern imports/notation'], [commandButtons.last(), 'modern verification commands']]) {
    await button.waitFor({state: 'attached'});
    const expected = await button.evaluate(button => document.getElementById(button.dataset.copy).textContent);
    assert(expected.length > 0);
    await both(page, button, expected, description);
  }
}
async function ulaArchive(page, url) {
  await page.goto(url, {waitUntil: 'domcontentloaded'});
  await page.waitForSelector('.copy-code[data-copy-next]', {state: 'attached'});
  const button = page.locator('button.copy-code[data-copy-next]').last();
  const info = await button.evaluate(button => {
    const pre = button.parentElement.nextElementSibling;
    return {file: pre.dataset.source, start: Number(pre.dataset.start), end: Number(pre.dataset.end),
      text: [...pre.querySelectorAll('.line-text')].map(line => line.textContent).join('\n')};
  });
  const expected = sourceSlice(info.file, info.start, info.end);
  assert.equal(info.text, expected);
  await both(page, button, expected, 'ULA archive proof excerpt');
  await checkCopy(page, button, expected, 'ULA archive blocked clipboard', 'blocked');
  const note = page.locator('pre.note-code').first();
  const noteExpected = await note.textContent();
  const noteButton = note.locator('xpath=preceding-sibling::*[1]').locator('.copy-code');
  await both(page, noteButton, noteExpected, 'ULA archive beginner example');
  const fileButton = page.locator('.module-actions .copy-code').first();
  const fileExpected = await fileButton.evaluate(button => {
    const pre = document.getElementById(button.dataset.code);
    return JSON.parse(document.getElementById('lean-sources').textContent)[pre.dataset.source];
  });
  await both(page, fileButton, fileExpected, 'ULA archive complete file');
}
async function sharedArchive(page, url, blocked = false) {
  await page.goto(url, {waitUntil: 'domcontentloaded'});
  const button = page.locator('.copy-excerpt').first();
  await button.waitFor({state: 'attached'});
  const info = await button.evaluate(button => ({file: button.dataset.source,
    start: Number(button.dataset.start), end: Number(button.dataset.end)}));
  const expected = sourceSlice(info.file, info.start, info.end);
  await both(page, button, expected, url.startsWith('file:') ? 'offline archive declaration' : 'shared archive declaration');
  if (blocked) await checkCopy(page, button, expected, 'archive blocked clipboard', 'blocked');
  const fileButton = page.locator('.module-actions .copy-source:not(.copy-excerpt)').first();
  const fileExpected = await fileButton.evaluate(button => JSON.parse(document.getElementById('lean-sources').textContent)[button.dataset.source]);
  await both(page, fileButton, fileExpected, 'shared archive complete file');
}
async function iplaArchive(page, url, offline = false) {
  await page.goto(url, {waitUntil: 'domcontentloaded'});
  const finalButton = page.locator('#exact-lean .archive-copy');
  const file = fs.readFileSync(path.join(REPO, 'IPLA/Theorem.lean'), 'utf8');
  const expected = 'theorem theorem1' + file.split('theorem theorem1', 2)[1].split(' := by', 1)[0];
  assert.equal(await page.locator('#exact-lean pre code').textContent(), expected);
  await both(page, finalButton, expected, offline ? 'offline IPLA theorem header' : 'IPLA theorem header');
  const link = page.locator('a[data-lean-source]').first();
  const modalInfo = await link.evaluate(link => ({file: link.dataset.leanSource,
    source: JSON.parse(document.getElementById('lean-source-data').textContent)[link.dataset.leanSource]}));
  assert.equal(modalInfo.source, fs.readFileSync(path.join(REPO, modalInfo.file), 'utf8'));
  await reveal(link);
  await link.click();
  await page.waitForSelector('#lean-source-dialog[open]');
  const modalButton = page.locator('#lean-source-copy');
  await both(page, modalButton, modalInfo.source, offline ? 'offline modal full file' : 'modal full file', '#lean-source-content .source-line');
  const capture = await page.evaluate(() => window.__copyCaptured[0]);
  assert(capture.modal, 'Modal fallback textarea remains inside the non-inert dialog');
  await checkCopy(page, modalButton, modalInfo.source, 'modal blocked clipboard', 'blocked', '#lean-source-content .source-line');
  await page.locator('#lean-source-close').click();
}
(async () => {
  checkModernCoverage();
  const server = http.createServer((request, response) => {
    let file;
    try {
      file = path.resolve(REPO, '.' + decodeURIComponent(new URL(request.url, 'http://localhost').pathname));
      if (!(file === REPO || file.startsWith(REPO + path.sep))) throw Error('Invalid path');
      if (fs.statSync(file).isDirectory()) file = path.join(file, 'index.html');
      const types = {'.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8'};
      response.writeHead(200, {'Content-Type': types[path.extname(file)] || 'text/plain; charset=utf-8'});
      fs.createReadStream(file).pipe(response);
    } catch (_) { response.writeHead(404); response.end('Not found'); }
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const base = `http://127.0.0.1:${server.address().port}/`;
  let browser;
  try {
    browser = await chromium.launch({executablePath: chrome, headless: true});
    const context = await browser.newContext({viewport: {width: 1024, height: 900}});
    await context.addInitScript(embeddedScript);
    const page = await context.newPage();
    page.setDefaultTimeout(5000);
    page.on('pageerror', error => errors.push(error.message));
    const modulePath = 'docs/modules/IPLA/Geometry.html';
    await modern(page, base + modulePath, true);
    await commands(page, base + 'IPLA/exposition/index.html');
    await ulaArchive(page, base + 'UnadjustedLangevin/exposition/dist/index.html');
    await sharedArchive(page, base + 'UnadjustedLangevin/LSI/exposition/proof.html', true);
    await sharedArchive(page, base + 'IPLA/LSI/exposition/proof.html');
    await sharedArchive(page, base + 'ProximalLangevin/exposition/proof.html');
    await iplaArchive(page, base + 'IPLA/exposition/proof.html');
    await modern(page, pathToFileURL(path.join(REPO, modulePath)).href);
    await sharedArchive(page, pathToFileURL(path.join(REPO, 'UnadjustedLangevin/LSI/exposition/proof.html')).href);
    await iplaArchive(page, pathToFileURL(path.join(REPO, 'IPLA/exposition/proof.html')).href, true);
    assert.deepEqual(errors, [], 'No uncaught browser exceptions');
    console.log(`Copy controls: ${count} browser cases passed; ${modernBlockCount} modern blocks on ${modernPageCount} pages have controls; exact Unicode source, rejection fallbacks, focus/selection restoration, blocked copies, offline pages, and full-file modal copying verified.`);
  } finally {
    if (browser) await browser.close();
    await new Promise(resolve => server.close(resolve));
  }
})().catch(error => { console.error(error.stack || error); process.exitCode = 1; });
