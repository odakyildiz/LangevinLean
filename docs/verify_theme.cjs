#!/usr/bin/env node
'use strict';
/** Local browser checks for automatic/explicit themes and responsive proof maps.
 * NODE_PATH=<bundled node_modules> node docs/verify_theme.cjs
 * No external resources, browser installation, or system clipboard writes.
 * THEME_QA_ROOT can select a generated checkout when running this file elsewhere.
 */
const fs = require('node:fs');
const fsp = require('node:fs/promises');
const http = require('node:http');
const os = require('node:os');
const path = require('node:path');
const {pathToFileURL} = require('node:url');
const {chromium, webkit} = require('playwright');
const ROOT = path.resolve(process.env.THEME_QA_ROOT || path.join(__dirname, '..'));
const VIEWPORTS = [320, 375, 768, 1024, 1440];
const HOMES = ['UnadjustedLangevin', 'IPLA', 'UnadjustedLangevin/LSI', 'IPLA/LSI',
  'ProximalLangevin', 'KineticLangevin', 'KIPLMC', 'PBGSO', 'LatentDiffusion', 'AverageLMC'].map(key => key + '/exposition/index.html');
const ARCHIVES = ['UnadjustedLangevin/exposition/dist/index.html', 'IPLA/exposition/proof.html',
  'UnadjustedLangevin/LSI/exposition/proof.html', 'IPLA/LSI/exposition/proof.html',
  'ProximalLangevin/exposition/proof.html'];
const MODULES = ['UnadjustedLangevin/CanonicalULA', 'IPLA/StrongLogConcavity',
  'UnadjustedLangevin/LSI/UnconditionalTheorem', 'IPLA/LSI/UnconditionalTheorem',
  'ProximalLangevin/SplittingEndpoint', 'KineticLangevin/PotentialContraction',
  'KIPLMC/Exponential'].map(name => 'docs/modules/' + name + '.html');
const THEME = '[data-theme-control]';
const CONNECTOR_FOCUS = process.env.THEME_QA_CONNECTORS_ONLY === '1';
const ROTATION_ONLY = process.env.THEME_QA_ROTATION_ONLY === '1';
const failures = [], checked = [], screenshots = [];
let browser, server, origin, output, active = 'setup';

function check(ok, message, details) {
  if (ok) return;
  const result = {test: active, message, ...(details === undefined ? {} : {details})};
  failures.push(result); console.error('FAIL ' + JSON.stringify(result));
}
async function run(label, fn) {
  active = label;
  try { await fn(); checked.push(label); console.log('Checked ' + label); }
  catch (error) { check(false, error.stack || error.message); }
}
async function localServer() {
  const types = {'.html':'text/html', '.js':'text/javascript', '.css':'text/css',
    '.svg':'image/svg+xml', '.woff':'font/woff', '.woff2':'font/woff2',
    '.ttf':'font/ttf', '.lean':'text/plain'};
  server = http.createServer(async (request, response) => {
    try {
      const name = decodeURIComponent(new URL(request.url, 'http://localhost').pathname);
      if (name === '/favicon.ico') { response.writeHead(204); response.end(); return; }
      let target = path.resolve(ROOT, '.' + name);
      if (target !== ROOT && !target.startsWith(ROOT + path.sep)) throw Error('Invalid path');
      if ((await fsp.stat(target)).isDirectory()) target = path.join(target, 'index.html');
      response.writeHead(200, {'Content-Type':types[path.extname(target)] || 'application/octet-stream',
        'Cache-Control':'no-store'}); response.end(await fsp.readFile(target));
    } catch (_) { response.writeHead(404); response.end('Not found'); }
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  origin = 'http://127.0.0.1:' + server.address().port;
}
async function context(width, scheme = 'dark', offline = false, blockedStorage = false) {
  const value = await browser.newContext({viewport:{width,height:1000}, colorScheme:scheme,
    reducedMotion:'reduce', offline, serviceWorkers:'block'});
  await value.route('**/*', route => {
    const url = new URL(route.request().url());
    if (url.origin === origin || ['file:','data:','blob:'].includes(url.protocol)) return route.continue();
    check(false, 'Page requested an external resource', url.href); return route.abort();
  });
  if (blockedStorage) await value.addInitScript(() => {
    Object.defineProperty(window, 'localStorage', {get(){throw new DOMException('Storage blocked', 'SecurityError');}});
  });
  return value;
}
function watch(page) {
  page.setDefaultTimeout(10000);
  page.on('pageerror', error => check(false, 'Uncaught page error', error.message));
}
async function goto(page, file, offline = false) {
  await page.goto(offline ? pathToFileURL(path.join(ROOT,file)).href : origin + '/' + file, {waitUntil:'load'});
  await page.evaluate(async () => {if (document.fonts) await document.fonts.ready;});
}
async function theme(page, expected, preference, print = false) {
  check(await page.locator(THEME).count() === 1, 'Page offers one accessible theme selector');
  await page.waitForFunction(value=>document.documentElement.dataset.theme===value.theme &&
    document.querySelector('[data-theme-control]')?.value===value.preference,{theme:expected,preference});
  const state = await page.evaluate(() => ({theme:document.documentElement.dataset.theme,
    selected:document.querySelector('[data-theme-control]')?.value,
    colorScheme:getComputedStyle(document.documentElement).colorScheme}));
  check(state.theme === expected && state.selected === preference, 'Theme matches preference and machine setting', state);
  check(state.colorScheme.includes(print ? 'light' : expected), 'Native browser controls use the active color scheme', state);
  const colors = await page.evaluate(() => {
    function rgb(value) {const m = value.match(/[\d.]+/g); return m ? m.map(Number) : [0,0,0,0];}
    function background(element) {
      let result = [255,255,255];
      const ancestors = []; for(let e=element;e;e=e.parentElement) ancestors.unshift(e);
      for(const e of ancestors) {const c=rgb(getComputedStyle(e).backgroundColor), a=c.length>3?c[3]:1;
        result=result.map((x,i)=>x*(1-a)+c[i]*a);}
      return result;
    }
    function luminance(c) {return c.slice(0,3).map(x=>x/255).map(x=>x<=.04045?x/12.92:((x+.055)/1.055)**2.4)
      .reduce((sum,x,i)=>sum+x*[.2126,.7152,.0722][i],0);}
    const selectors = ['h1', 'main p', '.diagram-node-title', '.diagram-node-detail', '.diagram-node-file',
      '.proof-node-label .node-title','.proof-node-label .node-detail','.proof-node-label .node-file',
      '.paper-reference .reference-scope','.paper-reference a','.lean-code .line-text',
      '.lean-code .tok-keyword','.lean-code .tok-comment','.lean-code .tok-tactic','.lean-code .tok-type',
      'dialog[open] .source-toolbar h2','dialog[open] .source-position',
      'dialog[open] .source-code .source-line'];
    const items=selectors.map(s=>document.querySelector(s)).filter(e=>e && e.getBoundingClientRect().width);
    const errors=items.map(e=>{const bg=background(e),fg=rgb(getComputedStyle(e).color), x=luminance(bg),y=luminance(fg);
      return {text:e.textContent.slice(0,80), ratio:(Math.max(x,y)+.05)/(Math.min(x,y)+.05),bg,fg};})
      .filter(x=>x.ratio<4.45);
    return {errors,bodyLuminance:luminance(background(document.body))};
  });
  check(colors.errors.length === 0, 'Body and diagram labels retain readable text contrast', colors.errors);
  check(expected==='dark'&&!print?colors.bodyLuminance<.15:colors.bodyLuminance>.7,
    'The active theme changes the actual page background',colors);
  const assumptionColors = await page.evaluate(() => {
    const probe = document.createElement('span');
    document.body.append(probe);
    const expected = {};
    for (const [property, token] of [['color','ink'], ['backgroundColor','bg'], ['borderLeftColor','border']]) {
      probe.style[property] = `var(--extra-assumption-${token})`;
      expected[property] = getComputedStyle(probe)[property];
    }
    probe.remove();
    return [...document.querySelectorAll('.added-assumption, [data-assumption-kind="added"]')]
      .flatMap(element => {
        const style = getComputedStyle(element);
        const errors = Object.entries(expected).filter(([property, value]) => style[property] !== value)
          .map(([property, value]) => ({property, expected:value, actual:style[property]}));
        return errors.length ? [{text:element.textContent.slice(0,100), errors}] : [];
      });
  });
  check(assumptionColors.length === 0,
    'Every extra assumption uses the shared orange text, background and border', assumptionColors);
}
async function layout(page) {
  await page.evaluate(()=>new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve))));
  const result = await page.evaluate(() => {
    const doc=Math.max(document.documentElement.scrollWidth,document.body.scrollWidth);
    const labels=[...document.querySelectorAll('.diagram-node-label,.proof-node-label')];
    const errors=[];
    for(const label of labels) {
      const r=label.getBoundingClientRect(); if(!r.width || !r.height) continue;
      if(label.scrollWidth>label.clientWidth+1 || label.scrollHeight>label.clientHeight+1)
        errors.push({issue:'label clipped',text:label.textContent.slice(0,100),width:r.width,height:r.height});
      if(/\\[\[(]/.test(label.textContent)) errors.push({issue:'raw TeX',text:label.textContent.slice(0,100)});
      const card=label.closest('a') || label; const c=card.getBoundingClientRect();
      for(const formula of label.querySelectorAll('.katex-html')) {
        const f=formula.getBoundingClientRect();
        if(f.left<c.left-1||f.right>c.right+1||f.top<c.top-1||f.bottom>c.bottom+1)
          errors.push({issue:'formula outside card',text:formula.textContent.slice(0,100),formula:[f.left,f.right,f.top,f.bottom],card:[c.left,c.right,c.top,c.bottom]});
      }
      if(r.width && parseFloat(getComputedStyle(label).fontSize)<12)
        errors.push({issue:'unreadably small diagram label',size:getComputedStyle(label).fontSize});
    }
    const links=[...document.querySelectorAll('.diagram-dependencies a,.proof-card-parents a')];
    const brokenParents=links.filter(a=>!document.getElementById(decodeURIComponent(a.hash.slice(1))))
      .map(a=>({text:a.textContent,href:a.getAttribute('href')}));
    const graphErrors=[];
    for(const root of document.querySelectorAll('[data-proof-diagram]')) {
      const grid=root.querySelector('[data-proof-grid]');if(!grid)continue;
      const nodes=[...grid.querySelectorAll('[data-node]')];
      const expected=nodes.flatMap(node=>(node.dataset.parents||'').split(/\s+/).filter(Boolean)
        .map(parent=>parent+'->'+node.dataset.node)).sort();
      const paths=[...root.querySelectorAll('path.diagram-connector')];
      const actual=paths.map(edge=>edge.dataset.from+'->'+edge.dataset.to).sort();
      if(innerWidth<=600) {
        if(actual.length)graphErrors.push({issue:'Mobile map retains connector paths',actual});
        continue;
      }
      if(JSON.stringify(actual)!==JSON.stringify(expected))
        graphErrors.push({issue:'Connectors differ from declared proof dependencies',expected,actual});
      const cards=nodes.map(node=>({id:node.dataset.node,rect:node.getBoundingClientRect()}));
      for(const edge of paths) {
        const matrix=edge.getScreenCTM();if(!matrix)continue;
        const otherCards=cards.filter(card=>card.id!==edge.dataset.from && card.id!==edge.dataset.to);
        const length=edge.getTotalLength();let collision;
        for(let distance=0;distance<=length;distance+=3) {
          const point=edge.getPointAtLength(distance),p=new DOMPoint(point.x,point.y).matrixTransform(matrix);
          collision=otherCards.find(({rect:r})=>p.x>r.left+1&&p.x<r.right-1&&p.y>r.top+1&&p.y<r.bottom-1);
          if(collision)break;
        }
        if(collision)graphErrors.push({issue:'Connector crosses another proof card',
          edge:edge.dataset.from+'->'+edge.dataset.to,card:collision.id});
      }
    }
    return {document:doc,viewport:innerWidth,labels:labels.length,errors,brokenParents,graphErrors,
      foreignObjects:document.querySelectorAll('#proof-map foreignObject').length,
      proofMapLabels:document.querySelectorAll('#proof-map .diagram-node-label,#proof-map .proof-node-label').length,
      rendered:document.querySelectorAll('#proof-map .katex').length,
      mathErrors:document.querySelectorAll('.katex-error').length};
  });
  check(result.document <= result.viewport+1, 'Page fits the viewport without horizontal page scrolling', result);
  check(result.errors.length===0, 'Diagram equations and labels fit readable native HTML cards',result.errors);
  check(result.foreignObjects===0, 'Embedded proof map avoids SVG foreignObject labels');
  check(result.mathErrors===0, 'Mathematics has no KaTeX rendering errors');
  check(result.brokenParents.length===0,'Proof dependency links reach their exact prerequisite cards',result.brokenParents);
  check(result.graphErrors.length===0,'Connector paths exactly match proof dependencies and avoid unrelated cards',result.graphErrors);
  if(result.proofMapLabels) check(result.rendered>0,'Proof map contains typeset mathematical equations');
}
async function copyAndReading(page) {
  const modern=page.locator('[data-copy-lean]').first();
  if(await modern.count()) {
    await page.evaluate(() => {Object.defineProperty(navigator,'clipboard',{configurable:true,
      value:{writeText:async value=>{window.__themeQACopy=value;}}});});
    const expected=await modern.evaluate(button=>[...button.closest('.code-wrap').querySelectorAll('.line-text')].map(e=>e.textContent).join('\n'));
    await modern.click(); await page.waitForFunction(()=>typeof window.__themeQACopy==='string');
    check(await page.evaluate(()=>window.__themeQACopy)===expected,'Copy Lean preserves the displayed plain source');
  }
  const read=page.locator('#reading-mode');
  if(await read.count()) {
    await read.selectOption('math');
    check(await page.locator('body').evaluate(e=>e.classList.contains('reading-math')||e.classList.contains('math-only')),
      'Reading controls still run with themes');
    await read.selectOption('paired');
  }
}
async function shot(page,name) {
  const map=page.locator('#proof-map');
  if(await map.count()) await map.scrollIntoViewIfNeeded();
  const file=path.join(output,name+'.png'); await page.screenshot({path:file,fullPage:false}); screenshots.push(file);
}
async function viewportRotation() {
  const ctx=await context(375,'dark'),page=await ctx.newPage();watch(page);
  await run('live viewport rotation 375-768-1440-375',async()=>{
    await goto(page,'IPLA/exposition/index.html');
    for(const width of [375,768,1440,375]) {
      await page.setViewportSize({width,height:1000});await theme(page,'dark','system');await layout(page);
    }
  });
  await ctx.close();
}
async function main() {
  output=process.env.THEME_QA_OUTPUT_DIR || await fsp.mkdtemp(path.join(os.tmpdir(),'langevin-theme-'));
  await fsp.mkdir(output,{recursive:true}); await localServer();
  const executablePath=process.env.PLAYWRIGHT_EXECUTABLE_PATH;
  const channel=process.env.PLAYWRIGHT_CHANNEL || 'chrome';
  browser=await chromium.launch({headless:true,...(executablePath?{executablePath}:{channel})});
  console.log('Browser '+browser.version()+', WebKit installed: '+fs.existsSync(webkit.executablePath()));
  if(ROTATION_ONLY) {await viewportRotation();return;}
  if(CONNECTOR_FOCUS) {
    for(const width of [375,768,1024,1440]) for(const scheme of ['light','dark']) {
      const ctx=await context(width,scheme),page=await ctx.newPage();watch(page);
      for(const file of [...HOMES,'IPLA/exposition/proof.html']) await run(width+':'+scheme+':connectors:'+file,async()=>{
        await goto(page,file);await theme(page,scheme,'system');await layout(page);
        if(file==='IPLA/exposition/index.html' && [375,768,1440].includes(width))
          await shot(page,width+'-'+scheme+'-ipla-connectors');
        if(file==='IPLA/exposition/proof.html' && width===768 && scheme==='dark')
          await shot(page,'768-dark-ipla-archive-connectors');
      });
      await ctx.close();
    }
    await viewportRotation();
    return;
  }
  for(const width of VIEWPORTS) for(const scheme of ['light','dark']) {
    const ctx=await context(width,scheme),page=await ctx.newPage();watch(page);
    for(const file of [...HOMES,...ARCHIVES]) await run(width+':'+scheme+':'+file,async()=>{
      await goto(page,file);await theme(page,scheme,'system');await layout(page);
      if(file==='IPLA/exposition/index.html' && [375,768].includes(width)) await shot(page,width+'-'+scheme+'-ipla-diagram');
    });
    await ctx.close();
  }
  const ctx=await context(768,'dark'),page=await ctx.newPage();watch(page);
  await run('system preference changes and manual persistence',async()=>{
    await goto(page,'index.html');await theme(page,'dark','system');
    await page.emulateMedia({colorScheme:'light'});await theme(page,'light','system');
    await page.locator(THEME).selectOption('dark');await theme(page,'dark','dark');
    await page.emulateMedia({colorScheme:'light'});await theme(page,'dark','dark');
    check(await page.evaluate(()=>localStorage.getItem('langevin-theme'))==='dark','Explicit preference is stored');
    await goto(page,HOMES[0]);await theme(page,'dark','dark');
    await page.reload({waitUntil:'load'});await theme(page,'dark','dark');
    await goto(page,ARCHIVES[0]);await theme(page,'dark','dark');
    await goto(page,HOMES[0]);await theme(page,'dark','dark');
    await page.locator(THEME).selectOption('light');await theme(page,'light','light');
    await page.emulateMedia({colorScheme:'dark'});await theme(page,'light','light');
    await page.locator(THEME).selectOption('system');await theme(page,'dark','system');
    await page.emulateMedia({colorScheme:'light'});await theme(page,'light','system');
    await copyAndReading(page);
  });
  await run('theme preferences synchronize between tabs',async()=>{
    const peer=await ctx.newPage();watch(peer);await peer.emulateMedia({colorScheme:'light'});
    await goto(peer,HOMES[1]);await theme(peer,'light','system');
    await page.locator(THEME).selectOption('dark');await theme(peer,'dark','dark');
    await peer.locator(THEME).selectOption('light');await theme(page,'light','light');
    await peer.evaluate(()=>localStorage.removeItem('langevin-theme'));
    await theme(page,'light','system');await peer.close();
  });
  for(const file of MODULES) await run('module controls:'+file,async()=>{
    await goto(page,file);await theme(page,'light','system');await layout(page);await copyAndReading(page);
  });
  for(const width of [375,768]) for(const scheme of ['light','dark']) await run(width+':'+scheme+':archived source dialog',async()=>{
    await page.setViewportSize({width,height:1000});
    await page.emulateMedia({colorScheme:scheme});await goto(page,'IPLA/exposition/proof.html');
    await page.locator(THEME).selectOption('system');
    await page.locator('a[data-lean-source]').first().click();
    check(await page.locator('#lean-source-dialog').evaluate(e=>e.open),'Source dialog opens');
    await theme(page,scheme,'system');await layout(page);
    const geometry=await page.locator('#lean-source-dialog').evaluate(e=>{const r=e.getBoundingClientRect();
      return {left:r.left,right:r.right,width:innerWidth,height:r.height};});
    check(geometry.left>=-1 && geometry.right<=geometry.width+1,'Source dialog fits the tablet viewport',geometry);
    await page.locator('#lean-source-close').click();
  });
  for(const scheme of ['light','dark']) for(const file of [HOMES[0],HOMES[1],...ARCHIVES]) {
    await run('print:'+scheme+':'+file,async()=>{
      await page.emulateMedia({media:'screen',colorScheme:scheme});await goto(page,file);
      await page.locator(THEME).selectOption('system');await page.emulateMedia({media:'print'});
      await theme(page,scheme,'system',true);
      check(!await page.locator(THEME).isVisible(),'Print layout hides the theme control');
      await page.emulateMedia({media:'screen'});
    });
  }
  await ctx.close();
  const blocked=await context(375,'dark',false,true),blockedPage=await blocked.newPage();watch(blockedPage);
  for(const file of ['index.html',HOMES[0],...ARCHIVES]) await run('blocked storage:'+file,async()=>{
    await goto(blockedPage,file);await theme(blockedPage,'dark','system');
    await blockedPage.locator(THEME).selectOption('light');await theme(blockedPage,'light','light');
    await blockedPage.locator(THEME).selectOption('system');await theme(blockedPage,'dark','system');
  });
  await blocked.close();
  const offline=await context(375,'dark',true),local=await offline.newPage();watch(local);
  for(const file of ['index.html',...HOMES,...ARCHIVES]) await run('offline file:'+file,async()=>{
    await goto(local,file,true);await local.locator(THEME).selectOption('system');await theme(local,'dark','system');
    await layout(local);await local.locator(THEME).selectOption('light');await theme(local,'light','light');
    await local.locator(THEME).selectOption('system');
  });
  await offline.close();
  await viewportRotation();
}
(async()=>{
  try {await main();} catch(error) {check(false,error.stack||error.message);}
  finally {
    if(browser) await browser.close();
    if(server?.listening) await new Promise(resolve=>server.close(resolve));
    const report={result:failures.length?'failed':'passed',cases:checked.length,
      viewports:ROTATION_ONLY?[375,768,1440]:CONNECTOR_FOCUS?[375,768,1024,1440]:VIEWPORTS,
      connectorFocus:CONNECTOR_FOCUS,rotationOnly:ROTATION_ONLY,
      webkitAvailable:fs.existsSync(webkit.executablePath()),externalRequestsAllowed:false,failures,screenshots};
    if(output) await fsp.writeFile(path.join(output,'report.json'),JSON.stringify(report,null,2)+'\n');
    console.log(JSON.stringify(report,null,2));process.exitCode=failures.length?1:0;
  }
})();
