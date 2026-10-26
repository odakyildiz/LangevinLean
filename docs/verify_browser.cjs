#!/usr/bin/env node
'use strict';
/**
 * Browser QA for the generated, offline proof atlas.
 *
 * Run after `python3 docs/build_site.py` with Playwright on NODE_PATH:
 *   node docs/verify_browser.cjs
 *
 * The script starts a loopback-only static server, blocks every external page
 * request, checks desktop and 375/320px mobile layouts, and repeats a local-file
 * smoke test in a browser context with network access disabled. Screenshots,
 * downloaded TeX/PDF examples, and a JSON report are saved outside the repository.
 *
 * Optional environment variables:
 *   PLAYWRIGHT_EXECUTABLE_PATH  Explicit Chromium/Chrome executable.
 *   PLAYWRIGHT_CHANNEL          Installed browser channel (e.g. chrome).
 *   BROWSER_QA_OUTPUT_DIR       Existing or new directory for test artifacts.
 */
const fs = require('node:fs');
const http = require('node:http');
const fsp = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');
const { pathToFileURL } = require('node:url');
const { chromium } = require('playwright');

const ROOT = path.resolve(process.env.BROWSER_QA_ROOT || path.join(__dirname, '..'));
const LIBRARIES = [
  { key: 'UnadjustedLangevin', label: 'ula', search: 'CanonicalULA.lean',
    legacy: 'UnadjustedLangevin/exposition/dist/index.html',
    modules: ['SharpContraction', 'CanonicalULA'] },
  { key: 'IPLA', label: 'ipla', search: 'Geometry.lean',
    legacy: 'IPLA/exposition/proof.html',
    modules: ['Geometry', 'StrongLogConcavity'] },
  { key: 'UnadjustedLangevin/LSI', label: 'ula-lsi', search: 'UnconditionalTheorem.lean',
    legacy: 'UnadjustedLangevin/LSI/exposition/proof.html',
    modules: ['GaussianEntropyIdentity', 'UnconditionalTheorem'] },
  { key: 'IPLA/LSI', label: 'ipla-lsi', search: 'UnconditionalTheorem.lean',
    legacy: 'IPLA/LSI/exposition/proof.html',
    modules: ['UnconditionalTheorem', 'Scaling'] },
  { key: 'ProximalLangevin', label: 'proximal', search: 'Moreau.lean',
    legacy: 'ProximalLangevin/exposition/proof.html',
    modules: ['Moreau', 'SplittingEndpoint'] },
  { key: 'KineticLangevin', label: 'kinetic', search: 'PotentialContraction.lean',
    modules: ['PotentialContraction', 'Gaussian'] },
  { key: 'KIPLMC', label: 'kiplmc', search: 'Exponential.lean',
    modules: ['Exponential', 'Splitting'] },
];
const VIEWPORTS = [
  { label: 'desktop', width: 1440, height: 1000 },
  { label: 'tablet', width: 768, height: 1024 },
  { label: 'mobile-375', width: 375, height: 812 },
  { label: 'mobile-320', width: 320, height: 760 },
];
const CASES = LIBRARIES.flatMap(library => [
  { library, kind: 'home', label: library.label + '-home',
    file: library.key + '/exposition/index.html' },
  ...library.modules.map(module => ({ library, kind: 'module',
    label: library.label + '-' + module,
    file: 'docs/modules/' + library.key + '/' + module + '.html' })),
]);
const failures = [];
const screenshots = [];
const downloads = [];
const expectedDownloadURLs = new Set();
const checked = [];
let requestCount = 0;
let activeCase = 'setup';
let browser;
let outputDir;
let origin;
let server;
let reportPlans;

function check(condition, message, details) {
  if (!condition) {
    const failure = { test: activeCase, message, ...(details === undefined ? {} : { details }) };
    failures.push(failure);
    console.error('FAIL [' + activeCase + '] ' + message +
      (details === undefined ? '' : '\n  ' + JSON.stringify(details)));
  }
  return Boolean(condition);
}

async function runCase(label, task) {
  activeCase = label;
  try {
    await task();
    checked.push(label);
    console.log('Checked ' + label);
  } catch (error) {
    check(false, error.message);
  }
}

async function launchBrowser() {
  const executablePath = process.env.PLAYWRIGHT_EXECUTABLE_PATH;
  const channel = process.env.PLAYWRIGHT_CHANNEL;
  if (executablePath || channel) {
    return chromium.launch({ headless: true, timeout: 30000,
      ...(executablePath ? { executablePath } : { channel }) });
  }
  try {
    return await chromium.launch({ headless: true, timeout: 30000 });
  } catch (bundledError) {
    try {
      return await chromium.launch({ headless: true, channel: 'chrome', timeout: 30000 });
    } catch (chromeError) {
      throw new Error('Could not launch bundled Chromium or installed Chrome. ' +
        'Set PLAYWRIGHT_EXECUTABLE_PATH or PLAYWRIGHT_CHANNEL.\n' +
        bundledError.message + '\n' + chromeError.message);
    }
  }
}

async function serveLocal(route, url) {
  const types = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
    '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8',
    '.tex': 'application/x-tex; charset=utf-8', '.pdf': 'application/pdf',
    '.bib': 'application/x-bibtex; charset=utf-8',
    '.lean': 'text/plain; charset=utf-8',
    '.md': 'text/plain; charset=utf-8', '.svg': 'image/svg+xml', '.png': 'image/png',
    '.woff': 'font/woff', '.woff2': 'font/woff2', '.ttf': 'font/ttf' };
  try {
    const pathname = decodeURIComponent(url.pathname);
    if (pathname === '/favicon.ico') return route.fulfill({ status: 204, body: '' });
    let target = path.resolve(ROOT, '.' + pathname);
    if (target !== ROOT && !target.startsWith(ROOT + path.sep)) {
      return route.fulfill({ status: 403, body: 'Outside repository' });
    }
    const stat = await fsp.stat(target);
    if (stat.isDirectory()) target = path.join(target, 'index.html');
    return route.fulfill({ status: 200,
      contentType: types[path.extname(target)] || 'application/octet-stream',
      headers: { 'Cache-Control': 'no-store' }, body: await fsp.readFile(target) });
  } catch (_) {
    return route.fulfill({ status: 404, contentType: 'text/plain; charset=utf-8', body: 'Not found' });
  }
}

async function startServer() {
  server = http.createServer((request, response) => {
    const route = { fulfill: async ({ status, contentType, headers, body }) => {
      response.writeHead(status, { ...(contentType ? { 'Content-Type': contentType } : {}), ...headers });
      response.end(body);
    } };
    serveLocal(route, new URL(request.url, 'http://127.0.0.1')).catch(error => {
      response.writeHead(500); response.end(error.message);
    });
  });
  await new Promise((resolve, reject) => {
    server.once('error', reject); server.listen(0, '127.0.0.1', resolve);
  });
  origin = 'http://127.0.0.1:' + server.address().port;
}

function watchPage(page) {
  page.setDefaultTimeout(10000);
  page.setDefaultNavigationTimeout(20000);
  page.on('pageerror', error => check(false, 'Uncaught page error', error.message));
  page.on('console', message => {
    if (message.type() === 'error') check(false, 'Browser console error', message.text());
  });
  page.on('request', request => { requestCount += 1; });
  page.on('requestfailed', request => {
    // Chromium may report the navigation request as aborted when handing it
    // to its download manager; the actual download result is checked below.
    if (expectedDownloadURLs.has(request.url()) && request.failure()?.errorText === 'net::ERR_ABORTED') return;
    check(false, 'Page resource request failed', { url: request.url(), error: request.failure() });
  });
  page.on('response', response => {
    if (response.status() >= 400) check(false, 'Page resource HTTP error', {
      url: response.url(), status: response.status() });
  });
}

async function contextFor(viewport, offline = false) {
  const context = await browser.newContext({ viewport: { width: viewport.width, height: viewport.height },
    deviceScaleFactor: 1, acceptDownloads: true, reducedMotion: 'reduce', offline,
    serviceWorkers: 'block' });
  if (!offline) {
    await context.grantPermissions(['clipboard-read', 'clipboard-write'], { origin });
  }
  await context.route('**/*', async route => {
    const url = new URL(route.request().url());
    if (url.origin === origin) return route.continue();
    if (url.protocol === 'file:' || url.protocol === 'data:' || url.protocol === 'blob:') return route.continue();
    check(false, 'External request on an offline proof page', url.href);
    return route.abort('blockedbyclient');
  });
  return context;
}

async function goto(page, url) {
  await page.goto(url, { waitUntil: 'load' });
  await page.evaluate(async () => { if (document.fonts) await document.fonts.ready; });
}

async function noPageOverflow(page) {
  const result = await page.evaluate(() => {
    const width = window.innerWidth;
    const documentWidth = Math.max(document.documentElement.scrollWidth, document.body.scrollWidth);
    const offenders = [...document.querySelectorAll('body *')].filter(element => {
      const rect = element.getBoundingClientRect();
      if (!rect.width || (rect.right <= width + 1 && rect.left >= -1)) return false;
      for (let parent = element.parentElement; parent; parent = parent.parentElement) {
        const style = getComputedStyle(parent);
        if (['auto', 'scroll', 'hidden', 'clip'].includes(style.overflowX)) return false;
      }
      return true;
    }).slice(0, 8).map(element => ({ tag: element.tagName, class: element.className?.baseVal ?? element.className,
      text: element.textContent.slice(0, 90), right: element.getBoundingClientRect().right }));
    return { viewport: width, document: documentWidth, offenders };
  });
  check(result.document <= result.viewport + 1, 'Page has horizontal overflow (inner scroll areas are allowed)', result);
}

async function mathematicalPage(page, item) {
  check(await page.locator('.katex').count() > 0, 'Expected pre-rendered KaTeX mathematics');
  check(await page.locator('.katex-error').count() === 0, 'KaTeX reports a rendering error');
  check(await page.locator('.pair .math-pane').count() > 0, 'Expected a parallel mathematical panel');
  check(await page.locator('.pair .lean-pane .lean-code').count() > 0, 'Expected exact Lean beside mathematics');
  check(await page.locator('.site-nav .brand').evaluate(element => new URL(element.href).pathname === '/index.html'),
    'Project-home navigation points to the repository home');
  if (item.kind === 'module') {
    check(await page.locator('.proof-step').count() > 0, 'Expected substantive module proof steps');
    check(await page.locator('.lean-code[data-role="declaration"]').count() > 0,
      'Expected complete declarations in module proof');
    check(await page.locator('#complete-source .lean-code[data-role="module"]').count() === 1,
      'Expected complete source with imports and variable context');
    const source = await page.locator('#complete-source .lean-code').textContent();
    check(source.includes('import ') && source.includes('theorem ') && source.includes(':='),
      'Complete module source includes imports, theorem statements, and proof bodies');
  } else {
    check(await page.locator('#main-results .lean-code[data-role="statement"]').count() > 0,
      'Expected source-derived main theorem headers');
    check(await page.locator('#verification .commands').count() > 0, 'Expected a verification workflow');
    check(await page.locator('#proof-map a.box').count() > 0, 'Expected navigable proof diagram boxes');
    await diagramTypesetting(page, '#proof-map', '.diagram-node-label');
  }
}

async function diagramTypesetting(page, selector, labelSelector) {
  const diagram = page.locator(selector);
  check(await diagram.locator('.katex').count() > 0, 'Diagram contains typeset mathematical formulas');
  const layout = await diagram.locator(labelSelector).evaluateAll(labels => labels.map(label => ({
    text: label.textContent.slice(0, 100),
    clipped: label.scrollWidth > label.clientWidth + 1 || label.scrollHeight > label.clientHeight + 1,
    rawTeX: /\\[\[(]/.test(label.textContent),
    scrollingFormulas: [...label.querySelectorAll('.katex')].some(formula =>
      ['auto', 'scroll', 'hidden', 'clip'].includes(getComputedStyle(formula).overflowX)),
  })).filter(label => label.clipped || label.rawTeX || label.scrollingFormulas));
  check(layout.length === 0, 'Diagram labels fit their boxes without raw TeX or inline scrollbars', layout);
}

async function readingModes(page) {
  const selector = page.locator('#reading-mode');
  for (const mode of ['paired', 'math', 'lean', 'paired']) {
    await selector.selectOption(mode);
    const result = await page.locator('.pair').first().evaluate(pair => ({
      math: getComputedStyle(pair.querySelector('.math-pane')).display !== 'none',
      lean: getComputedStyle(pair.querySelector('.lean-pane')).display !== 'none',
      stored: localStorage.getItem('langevin-reading'),
    }));
    check(result.math === (mode !== 'lean') && result.lean === (mode !== 'math'),
      'Reading mode shows the expected panels: ' + mode, result);
    check(result.stored === mode, 'Reading mode persists its selected value: ' + mode);
    await noPageOverflow(page);
  }
}

async function searchModules(page, item) {
  const input = page.locator('#module-search');
  const cards = page.locator('.module-card:not([hidden])');
  const initial = await cards.count();
  check(initial > 2, 'Expected a complete supporting-module directory');
  await input.fill(item.library.search);
  const matching = await cards.allTextContents();
  check(matching.length > 0 && matching.every(text => text.toLowerCase().includes(item.library.search.toLowerCase())),
    'Module search filters cards by the entered text', { query: item.library.search, matches: matching.length });
  check((await page.locator('#module-count').textContent()).trim() === matching.length + ' modules',
    'Module search count matches its visible cards');
  await input.fill('no_such_proof_browser_qa_81429');
  check(await cards.count() === 0, 'Zero-result module search hides every card');
  check((await page.locator('#module-count').textContent()).trim() === '0 modules',
    'Zero-result module search reports zero');
  check(await page.locator('.module-group:not([hidden])').count() === 0,
    'Zero-result module search hides empty groups');
  await input.fill('');
  check(await cards.count() === initial, 'Clearing module search restores every card');
}

async function diagramNavigation(page, item) {
  const box = page.locator('#proof-map a.box').first();
  const target = await box.getAttribute('href');
  check(target.endsWith('.html'), 'Diagram destination is an HTML proof page', target);
  await box.click();
  await page.waitForURL(url => url.pathname.includes('/docs/modules/') && url.pathname.endsWith('.html'));
  await page.waitForLoadState('load');
  await page.evaluate(async () => { if (document.fonts) await document.fonts.ready; });
  check(await page.locator('.proof-step .math-pane').count() > 0,
    'Diagram navigation opens fleshed-out mathematical proof');
  check(await page.locator('.proof-step .lean-pane .lean-code[data-role="declaration"]').count() > 0,
    'Diagram navigation opens complete Lean declarations beside the proof');
  await goto(page, origin + '/' + item.file);
}

async function latexDownload(page, item, viewport, link, suffix) {
  const href = await link.getAttribute('href');
  check(href && href.endsWith('.tex'), 'The page offers a LaTeX source download');
  expectedDownloadURLs.add(new URL(href, page.url()).href);
  const [download] = await Promise.all([page.waitForEvent('download'), link.click()]);
  check(download.suggestedFilename().endsWith('.tex'), 'LaTeX download has a TeX filename');
  const destination = path.join(outputDir, 'downloads', viewport.label + '-' + item.label + suffix + '.tex');
  await download.saveAs(destination);
  check(await download.failure() === null, 'LaTeX download succeeds');
  const source = await fsp.readFile(destination, 'utf8');
  check(source.includes('\\documentclass') && source.includes('\\begin{document}') && source.includes('\\end{document}'),
    'Downloaded LaTeX is a complete source document');
  check(source.includes('\\[') || source.includes('\\('), 'Downloaded proof includes mathematical statements');
  downloads.push(destination);
}

async function pdfDownload(page, item, viewport, texLink, suffix) {
  const texHref = await texLink.getAttribute('href');
  const href = texHref.replace(/(^|\/)latex\//, '$1pdf/').replace(/\.tex$/, '.pdf');
  const link = page.locator('a[download][href="' + href + '"]');
  if (!check(await link.count() === 1, 'Each full proof export offers one matching PDF download',
    { latex: texHref, pdf: href })) return;
  const url = new URL(href, page.url());
  expectedDownloadURLs.add(url.href);
  const [download] = await Promise.all([page.waitForEvent('download'), link.click()]);
  check(download.suggestedFilename().endsWith('.pdf'), 'PDF download has a PDF filename');
  const destination = path.join(outputDir, 'downloads', viewport.label + '-' + item.label + suffix + '.pdf');
  await download.saveAs(destination);
  check(await download.failure() === null, 'PDF download succeeds');
  const bytes = await fsp.readFile(destination);
  check(bytes.subarray(0, 5).toString('ascii') === '%PDF-', 'Downloaded proof has a PDF header');
  check(bytes.subarray(-1024).toString('latin1').trimEnd().endsWith('%%EOF'),
    'Downloaded proof has a complete PDF trailer');
  const source = path.resolve(ROOT, '.' + decodeURIComponent(url.pathname));
  if (check(source.startsWith(ROOT + path.sep), 'PDF export belongs to this repository', href)) {
    check(bytes.equals(await fsp.readFile(source)), 'Downloaded PDF matches its repository companion exactly');
  }
  downloads.push(destination);
}

async function proofDownloads(page, item, viewport) {
  const links = page.locator('a[download][href$=".tex"]');
  const count = await links.count();
  if (item.kind === 'module') check(count > 0, 'The module offers a LaTeX proof export');
  for (let index = 0; index < count; index++) {
    const link = links.nth(index);
    const suffix = count > 1 ? '-' + (index + 1) : '';
    await latexDownload(page, item, viewport, link, suffix);
    if (/(^|\/)FullProof\.tex$/.test(await link.getAttribute('href'))) {
      await pdfDownload(page, item, viewport, link, suffix);
    }
  }
}

function checkBibtex(value, expectedTitle, description) {
  check(/^\s*author\s*=\s*\{\{LangevinLean Project\}\}\s*,/mi.test(value),
    description + ' uses the exact corporate author LangevinLean Project');
  const field = value.match(/^\s*title\s*=\s*\{\{([\s\S]*?)\}\}\s*,/mi)?.[1];
  const title = field?.replace(/\\textbackslash\{\}/g, '\\')
    .replace(/\\([{}&%#_])/g, '$1');
  check(title === expectedTitle, description + ' names the expected report', {
    expected: expectedTitle, title,
  });
}

async function bibliographyCitation(page, item, viewport) {
  const panel = page.locator('details.citation-panel');
  if (!check(await panel.count() === 1, 'The page offers exactly one BibTeX citation panel')) return;
  const project = item.kind === 'project';
  const plan = project ? null : reportPlans[item.library.key];
  const expectedTitle = project ? 'LangevinLean: Formalized Langevin Algorithms' : plan.title;
  const expectedPath = project ? 'docs/bib/project.bib' : 'docs/bib/' + item.library.key + '.bib';
  const expectedBytes = await fsp.readFile(path.join(ROOT, expectedPath));
  checkBibtex(expectedBytes.toString('utf8'), expectedTitle, 'The repository BibTeX entry');
  const scroll = await page.evaluate(() => [window.scrollX, window.scrollY]);
  try {
    if (!await panel.evaluate(element => element.open)) await panel.locator('summary').click();
    check(await panel.evaluate(element => element.open), 'The citation panel expands');
    const code = panel.locator('pre code');
    check(await code.count() === 1, 'The expanded panel contains one BibTeX entry');
    const displayed = await code.textContent();
    check(displayed === expectedBytes.toString('utf8'),
      'The displayed citation matches its repository BibTeX entry exactly');
    await page.evaluate(() => navigator.clipboard.writeText('browser-qa-before-copy'));
    await panel.getByRole('button', { name: 'Copy BibTeX citation', exact: true }).click();
    await page.waitForFunction(() =>
      document.querySelector('.citation-panel button[data-copy]')?.textContent.trim() === 'Copied');
    const copied = await page.evaluate(() => navigator.clipboard.readText());
    check(copied === displayed, 'Copy BibTeX places the complete displayed entry on the clipboard');
    checkBibtex(copied, expectedTitle, 'The copied BibTeX entry');

    const link = panel.locator('a[download][href$=".bib"]');
    if (check(await link.count() === 1, 'The citation panel offers one BibTeX download')) {
      const href = await link.getAttribute('href');
      const url = new URL(href, page.url());
      check(decodeURIComponent(url.pathname) === '/' + expectedPath,
        'The BibTeX download points to the expected report entry', href);
      expectedDownloadURLs.add(url.href);
      const [download] = await Promise.all([page.waitForEvent('download'), link.click()]);
      check(download.suggestedFilename().endsWith('.bib'), 'BibTeX download has a .bib filename');
      const destination = path.join(outputDir, 'downloads',
        viewport.label + '-' + item.label + '-citation.bib');
      await download.saveAs(destination);
      check(await download.failure() === null, 'BibTeX download succeeds');
      const bytes = await fsp.readFile(destination);
      check(bytes.equals(expectedBytes), 'Downloaded BibTeX matches repository bytes exactly');
      checkBibtex(bytes.toString('utf8'), expectedTitle, 'The downloaded BibTeX entry');
      downloads.push(destination);
    }

    if (item.kind === 'module') {
      const source = item.file.replace(/^docs\/modules\//, '').replace(/\.html$/, '.lean');
      const location = plan.module_details[source];
      if (location) {
        const section = panel.locator('.small a[href*="#nameddest="]');
        if (check(await section.count() === 1, 'The module citation links its precise report section')) {
          const url = new URL(await section.getAttribute('href'), page.url());
          check(decodeURIComponent(url.pathname) === '/' + plan.pdf &&
            url.hash === '#nameddest=' + location.anchor,
          'The module citation targets its owning report and exact PDF destination', url.href);
          check((await section.textContent()).includes('Section ' + location.section),
            'The precise report citation displays its section number');
        }
      }
    }
    await noPageOverflow(page);
  } finally {
    await panel.evaluate(element => { element.open = false; });
    await page.evaluate(([x, y]) => window.scrollTo(x, y), scroll);
  }
}

async function screenshot(page, item, viewport) {
  const target = item.kind === 'home' ? '#main-results' : '.proof-step';
  await page.locator(target).first().evaluate(element => window.scrollTo(0,
    Math.max(0, window.scrollY + element.getBoundingClientRect().top - 18)));
  const destination = path.join(outputDir, viewport.label + '-' + item.label + '.png');
  await page.screenshot({ path: destination, fullPage: false, animations: 'disabled' });
  screenshots.push(destination);
}

async function legacyRedirect(page, library) {
  const hash = '#old-unknown-anchor-browser-qa';
  await page.goto(origin + '/' + library.key + '/exposition/index.html' + hash, { waitUntil: 'load' });
  await page.waitForURL(url => url.pathname === '/' + library.legacy && url.hash === hash);
  await page.waitForLoadState('load');
  await page.evaluate(async () => { if (document.fonts) await document.fonts.ready; });
  check(new URL(page.url()).pathname === '/' + library.legacy && new URL(page.url()).hash === hash,
    'Unknown old anchor routes to its preserved legacy document with the anchor intact');
}

async function projectLinks(page, viewport) {
  await goto(page, origin + '/index.html');
  await bibliographyCitation(page, { kind: 'project', label: 'project-home' }, viewport);
  const destination = path.join(outputDir, 'project-home-' + page.viewportSize().width + '.png');
  await page.screenshot({ path: destination, fullPage: true, animations: 'disabled' });
  screenshots.push(destination);
  check(await page.locator('.landing-card').count() === 7, 'Project home has six established theorem cards, the PBGSO source-based card and the particle entropy footnote');
  check((await page.locator('.landing-card h2').allTextContents()).includes('Unadjusted Langevin under Strong Convexity'),
    'ULA card states the strong convexity assumption');
  check((await page.locator('.landing-card h2').allTextContents()).includes('Interacting Particle Langevin under Strong Convexity'),
    'IPLA card states the strong convexity assumption');
  for (const library of LIBRARIES) {
    const relative = library.key + '/exposition/index.html';
    await page.locator('.landing-card a[href="' + relative + '"]').click();
    await page.waitForURL(url => url.pathname === '/' + relative);
    await page.waitForLoadState('load');
    await page.evaluate(async () => { if (document.fonts) await document.fonts.ready; });
    check(await page.locator('#main-results').count() === 1, 'Project card opens ' + library.label + ' overview');
    await page.locator('.site-nav .brand').click();
    await page.waitForURL(url => url.pathname === '/index.html');
    await page.waitForLoadState('load');
  }
  await page.locator('.landing-card a[href="PBGSO/exposition/index.html"]').click();
  await page.waitForURL(url => url.pathname === '/PBGSO/exposition/index.html');
  await page.waitForLoadState('load');
  check(await page.locator('#assumptions').count() === 1 && await page.locator('[data-source-result]').count() === 4,
    'PBGSO card opens four explicit paper theorem statements and their assumptions');
  check(await page.locator('#new-theory [data-new-theory]').count() === 2 &&
    await page.locator('[data-new-theory="A"]').count() === 1 &&
    await page.locator('[data-new-theory="B"]').count() === 1,
    'PBGSO New Theory contains exactly the final Theorem New A and Theorem New B');
  check(await page.locator('#standalone-verification').count() === 1 &&
    await page.locator('#proof-roadmap').count() === 1,
    'PBGSO provides runnable standalone verification and its mathematical proof roadmap');
  check(await page.locator('.module-card').count() === 0 &&
    await page.locator('a[href="technical.html"]').count() > 0,
    'The exhaustive PBGSO module catalog is separate from the primary theorem page');
  const assumptionColors = await page.evaluate(() => {
    const base = getComputedStyle(document.body).color;
    const added = [...document.querySelectorAll('.added-assumption[data-assumption-kind="added"]')];
    const interpreted = [...document.querySelectorAll('.interpretation-assumption[data-assumption-kind="interpretation"]')];
    return {base, added: added.map(e => getComputedStyle(e).color), interpreted: interpreted.map(e => getComputedStyle(e).color)};
  });
  check(assumptionColors.added.length > 0 && assumptionColors.interpreted.length > 0 &&
    assumptionColors.added.every(color => color !== assumptionColors.base) &&
    assumptionColors.interpreted.every(color => color !== assumptionColors.base) &&
    assumptionColors.added[0] !== assumptionColors.interpreted[0],
    'Added assumptions and semantic interpretations have distinct visible colors');
  await noPageOverflow(page);
  await page.locator('.site-nav .brand').click();
  await page.waitForURL(url => url.pathname === '/index.html');
  await noPageOverflow(page);
}

async function main() {
  const required = ['index.html', 'docs/assets/site.css', 'docs/assets/site.js', 'docs/full_proofs.json',
    'docs/bib/project.bib', ...LIBRARIES.map(library => 'docs/bib/' + library.key + '.bib'),
    ...CASES.map(item => item.file), ...LIBRARIES.map(library => library.legacy).filter(Boolean)];
  for (const file of required) {
    if (!fs.existsSync(path.join(ROOT, file))) throw new Error('Missing generated page/resource ' + file +
      '. Run python3 docs/build_site.py and the legacy builders before browser QA.');
  }
  reportPlans = JSON.parse(await fsp.readFile(path.join(ROOT, 'docs/full_proofs.json'), 'utf8'));
  outputDir = process.env.BROWSER_QA_OUTPUT_DIR
    ? path.resolve(process.env.BROWSER_QA_OUTPUT_DIR)
    : await fsp.mkdtemp(path.join(os.tmpdir(), 'langevin-browser-'));
  await fsp.mkdir(path.join(outputDir, 'downloads'), { recursive: true });
  console.log('Browser QA artifacts: ' + outputDir);
  await startServer();
  browser = await launchBrowser();
  console.log('Browser: ' + browser.version());
  for (const viewport of VIEWPORTS) {
    const context = await contextFor(viewport);
    const page = await context.newPage();
    watchPage(page);
    await runCase(viewport.label + ':project-home-navigation', () => projectLinks(page, viewport));
    for (const item of CASES) {
      await runCase(viewport.label + ':' + item.label, async () => {
        await goto(page, origin + '/' + item.file);
        await page.locator('#reading-mode').selectOption('paired');
        await mathematicalPage(page, item);
        await noPageOverflow(page);
        await readingModes(page);
        if (item.kind === 'home') {
          await searchModules(page, item);
          await diagramNavigation(page, item);
        }
        await bibliographyCitation(page, item, viewport);
        await screenshot(page, item, viewport);
        await proofDownloads(page, item, viewport);
      });
    }
    for (const library of LIBRARIES.filter(library => library.legacy)) {
      await runCase(viewport.label + ':' + library.label + ':legacy-anchor', () => legacyRedirect(page, library));
    }
    await context.close();
  }
  // Static local files must also work with the browser network turned off.
  const offline = await contextFor(VIEWPORTS[0], true);
  const local = await offline.newPage();
  watchPage(local);
  for (const item of CASES) {
    await runCase('offline-file:' + item.label, async () => {
      await goto(local, pathToFileURL(path.join(ROOT, item.file)).href);
      check(await local.locator('.katex').count() > 0, 'Offline local file contains rendered mathematics');
      check(await local.locator('.katex-error').count() === 0, 'Offline local math renders without errors');
      if (item.kind === 'home') await diagramTypesetting(local, '#proof-map', '.diagram-node-label');
      await local.locator('#reading-mode').selectOption('math');
      check(await local.locator('body.reading-math').count() === 1, 'Offline local file runs its reading controls');
      await local.locator('#reading-mode').selectOption('paired');
      await noPageOverflow(local);
    });
  }
  await runCase('offline-file:archived-ipla-diagram', async () => {
    await goto(local, pathToFileURL(path.join(ROOT, 'IPLA/exposition/proof.html')).href);
    await diagramTypesetting(local, '#proof-map', '.proof-node-label');
    check(await local.locator('#proof-map a.proof-node').count() === 14, 'Archived diagram retains all proof links');
  });
  await runCase('offline-file:standalone-ipla-svg', async () => {
    await goto(local, pathToFileURL(path.join(ROOT, 'IPLA/exposition/proof-map.svg')).href);
    await diagramTypesetting(local, 'svg.proof-svg', '.proof-node-label');
    check(await local.locator('.katex-error').count() === 0, 'Standalone SVG math renders without errors');
    check(await local.evaluate(() => [...document.fonts].every(font => font.status !== 'error')),
      'Standalone SVG embeds working mathematical fonts');
  });
  await offline.close();
}

(async () => {
  try { await main(); } catch (error) { check(false, error.stack || error.message); }
  finally {
    if (browser) await browser.close();
    if (server && server.listening) await new Promise(resolve => server.close(resolve));
    const report = { browserQA: failures.length === 0 ? 'passed' : 'failed',
      cases: checked.length, pageResourceRequests: requestCount, externalRequestsAllowed: false,
      viewports: VIEWPORTS, failures, screenshots, downloads };
    if (outputDir) {
      await fsp.writeFile(path.join(outputDir, 'report.json'), JSON.stringify(report, null, 2) + '\n');
      console.log('Screenshots and detailed report: ' + outputDir);
    }
    console.log(JSON.stringify({ result: report.browserQA, checkedCases: checked.length,
      screenshots: screenshots.length, latexDownloads: downloads.filter(file => file.endsWith('.tex')).length,
      pdfDownloads: downloads.filter(file => file.endsWith('.pdf')).length,
      bibtexDownloads: downloads.filter(file => file.endsWith('.bib')).length, failures: failures.length }, null, 2));
    process.exitCode = failures.length ? 1 : 0;
  }
})();
