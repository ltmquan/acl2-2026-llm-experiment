// Writes tests-topologies.lsp: for each topology in model.js, attaches matching ACL2 functions with defattach and
// checks the JavaScript port against ACL2 on random legal executions (final state, pre-inputs, post-inputs,
// complete-segment-p, state-equiv of the reordering). Load after (include-book "solution"); prints Tn (t t t t t).
const M = require(__dirname + '/model.js');
let seed = 23; const rnd = (n) => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n; };
const lit = (e) => (e.length ? "'(" + e.map((x) => '(' + x.join(' ') + ')').join(' ') + ')' : 'nil');
const qlist = (l) => (l.length ? "'(" + l.join(' ') + ')' : 'nil');
const uniq = (l) => [...new Set(l)];
const out = [`(defun c-compute (p ls) (declare (xargs :guard t)) (declare (ignore p)) (case ls (l1 'a1) (l2 'a2) (a1 'b1) (t ls)))
(defun c-receive (p j m ls) (declare (xargs :guard t)) (list :rcv p j m ls))
(defun c-send-p (p k ls) (declare (xargs :guard t)) (declare (ignore p k)) (member-equal ls '(a1 a2)))
(defun c-make-msg (p k ls) (declare (xargs :guard t)) (declare (ignore k ls)) (if (equal p 1) 'm1 'm2))
(defun c-init (p) (declare (xargs :guard t)) (if (equal p 1) 'l1 'l2))`];
let n = 0;
for (const [name, T] of Object.entries(M.CONFIGS)) {
  M.setTopology(name);
  const f = name.replace(/[^a-z]/g, '');
  const tbl = (m) => '(case p ' + Object.entries(m).map(([k, v]) => `(${k} ${qlist(v)})`).join(' ') + ' (t nil))';
  out.push(`(defun c-in-${f} (p) (declare (xargs :guard t)) ${tbl(T.in)})
(defun c-out-${f} (p) (declare (xargs :guard t)) ${tbl(T.out)})
(defun c-procs-${f} () (declare (xargs :guard t)) ${qlist(T.procs)})
(defattach (app-compute c-compute) (app-receive c-receive) (app-send-p c-send-p) (app-make-msg c-make-msg)
  (in-nbrs c-in-${f}) (out-nbrs c-out-${f}) (init-local c-init) (sys-procs c-procs-${f}))`);
  const procs = uniq(T.procs), C = [];
  for (const p of procs) { C.push([p, ':compute'], [p, ':checkpoint']); for (const j of procs) if (j !== p) C.push([p, ':receive', j]); }
  for (let t = 0; t < 30; t++) {
    let st = M.initState(); const pre = [];
    for (let i = 0; i < rnd(4); i++) { const c = C.filter((x) => M.legalInput(st, x)); const x = c[rnd(c.length)]; pre.push(x); st = M.clStep(st, x); }
    const seg = [[procs[rnd(procs.length)], ':checkpoint']]; st = M.clStep(st, seg[0]);
    for (let i = 0; i < 2 + rnd(9); i++) { const c = C.filter((x) => M.legalInput(st, x)); if (!c.length) break; const x = c[rnd(c.length)]; seg.push(x); st = M.clStep(st, x); }
    const st0 = M.clRun(M.initState(), pre), fin = M.clRun(st0, seg), sid = M.segmentTarget(st0, seg);
    const p = M.preInputs(sid, st0, seg), q = M.postInputs(sid, st0, seg), S0 = `(cl-run (init-state) ${lit(pre)})`;
    out.push(`(cw "T${n++} ${name} ~x0~%" (list (equal (cl-run ${S0} ${lit(seg)}) ${M.toAcl2(fin)})
  (equal (pre-inputs (segment-target ${S0} ${lit(seg)}) ${S0} ${lit(seg)}) ${lit(p)})
  (equal (post-inputs (segment-target ${S0} ${lit(seg)}) ${S0} ${lit(seg)}) ${lit(q)})
  (equal (complete-segment-p ${S0} ${lit(seg)}) ${M.completeSegmentP(st0, seg) ? 't' : 'nil'})
  (equal (state-equiv (cl-run ${S0} (append ${lit(p)} ${lit(q)})) (cl-run ${S0} ${lit(seg)})) ${M.stateEquiv(M.clRun(st0, [...p, ...q]), fin) ? 't' : 'nil'})))`);
  }
}
require('fs').writeFileSync(__dirname + '/tests-topologies.lsp', out.join('\n') + '\n');
console.log(n, 'tests written');
