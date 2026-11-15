// For each topology: enumerate every legal segment of length <= MAXLEN from st (after the prefix) that starts
// with a :checkpoint. A segment is extended only while the target snapshot is incomplete, so every segment that
// reaches completion is a complete segment (complete-segment-p). For each one, check MAIN's conclusion
// (state-equiv and equality of final states) and the legality of (append pre post). Also check, on every
// enumerated segment, that every adjacent post/pre swap commutes.
const M = require(__dirname + '/model.js');
const PREFIX = [[1, ':compute'], [2, ':compute']];
const MAXLEN = +(process.argv[2] || 7);
const uniq = (l) => [...new Set(l)];
for (const name of Object.keys(M.CONFIGS)) {
  M.setTopology(name);
  const procs = uniq(M.APP['sys-procs']());
  const C = [];
  for (const p of procs) { C.push([p, ':compute'], [p, ':checkpoint']); for (const j of procs) if (j !== p) C.push([p, ':receive', j]); }
  const st0 = M.clRun(M.initState(), PREFIX);
  const r = { enumerated: 0, complete: 0, completeWithInversions: 0, mainHolds: 0, equalFinal: 0, reorderedLegal: 0, swaps: 0, nonCommuting: 0, completeMismatch: 0 };
  let example = null;
  function check(seg) {
    r.enumerated++;
    const sid = M.segmentTarget(st0, seg), lab = M.classify(sid, st0, seg);
    let items = seg.map((x, i) => ({ x, l: lab[i] })), inv = 0;
    for (;;) {
      const k = items.findIndex((it, i) => it.l === 'post' && items[i + 1] && items[i + 1].l === 'pre'); if (k < 0) break;
      inv++; const S = M.clRun(st0, items.slice(0, k).map((i) => i.x)), x = items[k].x, y = items[k + 1].x;
      r.swaps++; if (!M.equal(M.clStep(M.clStep(S, x), y), M.clStep(M.clStep(S, y), x))) r.nonCommuting++;
      [items[k], items[k + 1]] = [items[k + 1], items[k]];
    }
    return { sid, inv };
  }
  function dfs(seg, st) {
    const { sid, inv } = check(seg);
    const done = M.checkpointComplete(sid, st);
    if (done) {
      r.complete++;
      if (!M.completeSegmentP(st0, seg)) r.completeMismatch++;
      const pre = M.preInputs(sid, st0, seg), post = M.postInputs(sid, st0, seg);
      const F1 = M.clRun(st0, [...pre, ...post]), F2 = M.clRun(st0, seg);
      if (M.stateEquiv(F1, F2)) r.mainHolds++;
      if (M.equal(F1, F2)) r.equalFinal++;
      if (M.legalExec(st0, [...pre, ...post])) r.reorderedLegal++;
      if (inv > 0) { r.completeWithInversions++; if (!example || inv > example.inv || (inv === example.inv && seg.length < example.seg.length)) example = { seg, inv }; }
      return;                       // a complete segment must end at completion
    }
    if (seg.length >= MAXLEN) return;
    for (const x of C) if (M.legalInput(st, x)) dfs([...seg, x], M.clStep(st, x));
  }
  for (const p of procs) dfs([[p, ':checkpoint']], M.clStep(st0, [p, ':checkpoint']));
  console.log(name, JSON.stringify(r));
  console.log('  example:', example ? JSON.stringify(example) : 'none');
}
