// For each topology: random legal segments from the same prefix; count complete ones, check every
// adjacent post/pre swap commutes, and pick a short complete example that needs reordering.
const M = require(__dirname + '/model.js');
const PREFIX = [[1, ':compute'], [2, ':compute']];
let seed = 5; const rnd = (n) => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n; };
const uniq = (l) => [...new Set(l)];
for (const name of Object.keys(M.CONFIGS)) {
  M.setTopology(name);
  const procs = uniq(M.APP['sys-procs']());
  const C = [];
  for (const p of procs) { C.push([p, ':compute'], [p, ':checkpoint']); for (const j of procs) if (j !== p) C.push([p, ':receive', j]); }
  const st0 = M.clRun(M.initState(), PREFIX);
  let n = 0, complete = 0, swaps = 0, bad = 0, illegal = 0, best = null;
  for (let t = 0; t < 3000; t++) {
    const seg = [[procs[rnd(procs.length)], ':checkpoint']]; let st = M.clStep(st0, seg[0]);
    for (let i = 0; i < 1 + rnd(10); i++) { const c = C.filter((x) => M.legalInput(st, x)); if (!c.length) break; const x = c[rnd(c.length)]; seg.push(x); st = M.clStep(st, x); }
    n++;
    const sid = M.segmentTarget(st0, seg), lab = M.classify(sid, st0, seg);
    let items = seg.map((x, i) => ({ x, l: lab[i] })), inv = 0;
    for (;;) {
      const k = items.findIndex((it, i) => it.l === 'post' && items[i + 1] && items[i + 1].l === 'pre'); if (k < 0) break;
      inv++; const S = M.clRun(st0, items.slice(0, k).map((i) => i.x)), x = items[k].x, y = items[k + 1].x;
      swaps++; if (!M.equal(M.clStep(M.clStep(S, x), y), M.clStep(M.clStep(S, y), x))) bad++;
      if (!(M.legalInput(S, y) && M.legalInput(M.clStep(S, y), x))) illegal++;
      [items[k], items[k + 1]] = [items[k + 1], items[k]];
    }
    if (M.completeSegmentP(st0, seg)) {
      complete++;
      if (inv > 0 && (!best || seg.length < best.seg.length || (seg.length === best.seg.length && inv > best.inv))) best = { seg, inv };
    }
  }
  console.log(name, JSON.stringify({ segments: n, complete, swaps, nonCommuting: bad, illegalSwapped: illegal }));
  console.log('  example:', best ? JSON.stringify(best) : 'none (no complete segment needs reordering)');
}
