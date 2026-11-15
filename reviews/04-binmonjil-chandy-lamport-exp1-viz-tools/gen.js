const M = require(__dirname + '/model.js');
let seed = 7; const rnd = (n) => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n; };
const cands = (st) => [[1, ':compute'], [2, ':compute'], [1, ':checkpoint'], [2, ':checkpoint'], [1, ':receive', 2], [2, ':receive', 1]].filter((x) => M.legalInput(st, x));
const lit = (e) => "'(" + e.map((x) => '(' + x.join(' ') + ')').join(' ') + ')';
const out = [];
const fixed = [[[1, ':compute'], [2, ':compute']], [[1, ':checkpoint'], [1, ':compute'], [1, ':receive', 2], [2, ':receive', 1], [2, ':receive', 1], [1, ':receive', 2]]];
const tests = [fixed];
for (let t = 0; t < 40; t++) {
  let st = M.initState(); const pre = [];
  for (let i = 0; i < rnd(4); i++) { const c = cands(st); const x = c[rnd(c.length)]; pre.push(x); st = M.clStep(st, x); }
  const seg = [[1 + rnd(2), ':checkpoint']]; st = M.clStep(st, seg[0]);
  for (let i = 0; i < 2 + rnd(10); i++) { const c = cands(st); if (!c.length) break; const x = c[rnd(c.length)]; seg.push(x); st = M.clStep(st, x); }
  tests.push([pre, seg]);
}
tests.forEach(([pre, seg], i) => {
  const st0 = M.clRun(M.initState(), pre), fin = M.clRun(st0, seg), sid = M.segmentTarget(st0, seg);
  const p = M.preInputs(sid, st0, seg), q = M.postInputs(sid, st0, seg);
  const S0 = `(cl-run (init-state) ${lit(pre)})`;
  out.push(`(cw "T${i} ~x0~%" (list (equal (cl-run ${S0} ${lit(seg)}) ${M.toAcl2(fin)})
     (equal (pre-inputs (segment-target ${S0} ${lit(seg)}) ${S0} ${lit(seg)}) ${lit(p) === "'()" ? 'nil' : lit(p)})
     (equal (post-inputs (segment-target ${S0} ${lit(seg)}) ${S0} ${lit(seg)}) ${lit(q) === "'()" ? 'nil' : lit(q)})
     (equal (complete-segment-p ${S0} ${lit(seg)}) ${M.completeSegmentP(st0, seg) ? 't' : 'nil'})
     (equal (state-equiv (cl-run ${S0} (append ${lit(p) === "'()" ? 'nil' : lit(p)} ${lit(q) === "'()" ? 'nil' : lit(q)})) (cl-run ${S0} ${lit(seg)})) ${M.stateEquiv(M.clRun(st0, [...p, ...q]), fin) ? 't' : 'nil'})))`);
  if (M.completeSegmentP(st0, seg)) out.push(`(cw "C${i} complete~%")`);
});
require('fs').writeFileSync(__dirname + '/tests.lsp', out.join('\n') + '\n');
console.log(tests.length, 'tests;', out.filter((l) => l.startsWith('(cw "C')).length, 'complete segments');
