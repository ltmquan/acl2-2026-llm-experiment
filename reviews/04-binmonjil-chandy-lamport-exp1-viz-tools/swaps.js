const M = require(__dirname + '/model.js');
let seed = 11; const rnd = (n) => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n; };
const C = [[1, ':compute'], [2, ':compute'], [1, ':checkpoint'], [2, ':checkpoint'], [1, ':receive', 2], [2, ':receive', 1]];
const st0 = M.clRun(M.initState(), [[1, ':compute'], [2, ':compute']]);
let swaps = 0, bad = 0, illegal = 0, finalBad = 0, complete = 0;
for (let t = 0; t < 2000; t++) {
  const seg = [[1 + rnd(2), ':checkpoint']]; let st = M.clStep(st0, seg[0]);
  for (let i = 0; i < 2 + rnd(12); i++) { const c = C.filter((x) => M.legalInput(st, x)); if (!c.length) break; const x = c[rnd(c.length)]; seg.push(x); st = M.clStep(st, x); }
  if (M.completeSegmentP(st0, seg)) complete++;
  const sid = M.segmentTarget(st0, seg); let items = seg.map((x, i) => ({ x, l: M.classify(sid, st0, seg)[i] }));
  for (;;) {
    const k = items.findIndex((it, i) => it.l === 'post' && items[i + 1] && items[i + 1].l === 'pre'); if (k < 0) break;
    const S = M.clRun(st0, items.slice(0, k).map((i) => i.x)), x = items[k].x, y = items[k + 1].x;
    swaps++; if (!M.equal(M.clStep(M.clStep(S, x), y), M.clStep(M.clStep(S, y), x))) bad++;
    if (!(M.legalInput(S, y) && M.legalInput(M.clStep(S, y), x))) illegal++;
    [items[k], items[k + 1]] = [items[k + 1], items[k]];
  }
  if (!M.equal(M.clRun(st0, items.map((i) => i.x)), M.clRun(st0, seg))) finalBad++;
}
console.log({ segments: 2000, complete, swaps, nonCommuting: bad, illegalSwapped: illegal, finalDiffers: finalBad });
