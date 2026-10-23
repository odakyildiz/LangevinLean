/* Keep all mathematical labels in HTML. This SVG layer draws only proof edges. */
(() => {
  'use strict';
  const NS = 'http://www.w3.org/2000/svg';
  let diagramId = 0;
  const create = (name, attrs = {}) => {
    const element = document.createElementNS(NS, name);
    Object.entries(attrs).forEach(([key, value]) => element.setAttribute(key, value));
    return element;
  };
  document.querySelectorAll('[data-proof-diagram]').forEach(root => {
    const grid = root.querySelector('[data-proof-grid]');
    if (!grid || root.querySelector(':scope > .diagram-connectors')) return;
    const markerId = 'proof-edge-arrow-' + (++diagramId);
    const svg = create('svg', {'class':'diagram-connectors', 'aria-hidden':'true', focusable:'false'});
    const defs = create('defs');
    const marker = create('marker', {id:markerId, viewBox:'0 0 10 10', refX:'9', refY:'5', markerWidth:'6', markerHeight:'6', orient:'auto'});
    marker.append(create('path', {d:'M 0 0 L 10 5 L 0 10 z', 'class':'diagram-arrowhead'}));
    defs.append(marker);
    svg.append(defs);
    const edges = create('g');
    svg.append(edges);
    root.insertBefore(svg, grid);
    let frame = 0;
    const draw = () => {
      frame = 0;
      edges.replaceChildren();
      if (window.matchMedia('(max-width: 600px)').matches) return;
      const bounds = root.getBoundingClientRect();
      if (!bounds.width || !bounds.height) return;
      svg.setAttribute('viewBox', `0 0 ${bounds.width} ${bounds.height}`);
      const nodes = [...grid.querySelectorAll('[data-node]')].map(element => {
        const rect = element.getBoundingClientRect();
        return {element, id:element.dataset.node, left:rect.left-bounds.left, right:rect.right-bounds.left,
          top:rect.top-bounds.top, bottom:rect.bottom-bounds.top,
          x:(rect.left+rect.right)/2-bounds.left, y:(rect.top+rect.bottom)/2-bounds.top};
      });
      const byId = new Map(nodes.map(node => [node.id, node]));
      const rowTops = [...new Set(nodes.map(node => Math.round(node.top)))].sort((a,b) => a-b);
      const rowIndex = node => rowTops.findIndex(y => Math.abs(y-node.top) < 2);
      let edgeNumber = 0;
      for (const child of nodes) {
        const parents = (child.element.dataset.parents || '').split(/\s+/).filter(Boolean);
        for (const parentId of parents) {
          const parent = byId.get(parentId);
          if (!parent) continue;
          const parentRow = rowIndex(parent), childRow = rowIndex(child);
          let route;
          if (parentRow === childRow) {
            const leftToRight = parent.x < child.x;
            const fromX = leftToRight ? parent.right+1 : parent.left-1;
            const toX = leftToRight ? child.left-2 : child.right+2;
            const between = nodes.some(node => node !== parent && node !== child && rowIndex(node) === childRow &&
              node.x > Math.min(parent.x,child.x) && node.x < Math.max(parent.x,child.x));
            if (!between) route = `M ${fromX} ${parent.y} H ${toX}`;
            else {
              const above = Math.min(parent.top,child.top)-12;
              route = `M ${parent.x} ${parent.top-1} V ${above} H ${child.x} V ${child.top-2}`;
            }
          } else {
            const start = parent.bottom+1, end = child.top-2;
            if (childRow === parentRow+1) {
              const middle = (parent.bottom+child.top)/2;
              route = `M ${parent.x} ${start} V ${middle} H ${child.x} V ${end}`;
            } else {
              // Skip-layer edges stay in the outer padding, never through cards.
              const parentRowBottom = Math.max(...nodes.filter(node => rowIndex(node) === parentRow).map(node => node.bottom));
              const nextTop = rowTops[parentRow+1] ?? parentRowBottom+24;
              const childPreviousBottom = Math.max(...nodes.filter(node => rowIndex(node) === childRow-1).map(node => node.bottom));
              const exitY = (parentRowBottom+nextTop)/2;
              const entryY = (childPreviousBottom+child.top)/2;
              const lane = 7+2*(edgeNumber%3);
              const gutter = child.x < bounds.width/2 ? lane : bounds.width-lane;
              route = `M ${parent.x} ${start} V ${exitY} H ${gutter} V ${entryY} H ${child.x} V ${end}`;
            }
          }
          edges.append(create('path', {d:route, 'class':'diagram-connector', 'data-from':parentId, 'data-to':child.id,
            'marker-end':`url(#${markerId})`, 'vector-effect':'non-scaling-stroke'}));
          edgeNumber++;
        }
      }
    };
    const schedule = () => { if (!frame) frame = requestAnimationFrame(draw); };
    if ('ResizeObserver' in window) {
      const observer = new ResizeObserver(schedule);
      observer.observe(root);
      observer.observe(grid);
    }
    window.addEventListener('resize', schedule, {passive:true});
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(schedule);
    schedule();
  });
})();
