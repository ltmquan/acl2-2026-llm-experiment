// JavaScript port of the model in 04-binmonjil-chandy-lamport/exp1/solution.lisp.
// Function names follow the ACL2 ones (kebab-case -> camelCase); see NAMES below.
// Lisp data: symbols/keywords are strings, numbers are numbers, nil is null,
// proper lists are arrays, dotted pairs are Pair objects, records (misc/records) are Rec.

class Pair { constructor(car, cdr) { this.car = car; this.cdr = cdr; } }

function cons(a, b) {
  if (b === null) return [a];
  if (Array.isArray(b)) return [a, ...b];
  return new Pair(a, b);
}
function car(x) { return Array.isArray(x) ? (x.length ? x[0] : null) : x instanceof Pair ? x.car : null; }
function cdr(x) {
  if (Array.isArray(x)) return x.length > 1 ? x.slice(1) : null;
  return x instanceof Pair ? x.cdr : null;
}
function consp(x) { return (Array.isArray(x) && x.length > 0) || x instanceof Pair; }
function listOf(x) { return Array.isArray(x) ? x : []; }       // proper-list view (nil -> [])
function nil(x) { return x === null || (Array.isArray(x) && x.length === 0) || (x instanceof Rec && x.size() === 0); }
function norm(x) { return nil(x) ? null : x; }

// canonical printed form (used for equality and record keys)
function show(x) {
  if (x === null) return 'nil';
  if (typeof x === 'number') return String(x);
  if (typeof x === 'string') return x;
  if (x instanceof Pair) return '(' + show(x.car) + ' . ' + show(x.cdr) + ')';
  if (Array.isArray(x)) return x.length ? '(' + x.map(show).join(' ') + ')' : 'nil';
  if (x instanceof Rec) return x.show();
  throw new Error('show: ' + x);
}
function equal(a, b) { return show(norm(a)) === show(norm(b)); }

// misc/records: (g k r), (s k v r); nil-valued fields are absent.
class Rec {
  constructor(m) { this.m = m || new Map(); }
  size() { return this.m.size; }
  keys() { return [...this.m.values()].map(([k]) => k); }
  show() {
    const ents = [...this.m.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    return ents.length ? '{' + ents.map(([ks, [, v]]) => ks + ' ' + show(v)).join(', ') + '}' : 'nil';
  }
}
function g(k, r) { if (!(r instanceof Rec)) return null; const e = r.m.get(show(k)); return e ? e[1] : null; }
function s(k, v, r) {
  const m = new Map(r instanceof Rec ? r.m : undefined);
  v = norm(v);
  if (v === null) m.delete(show(k)); else m.set(show(k), [k, v]);
  return m.size ? new Rec(m) : null;
}
const memberEqual = (x, l) => listOf(l).some((y) => equal(x, y));
const removeEqual = (x, l) => norm(listOf(l).filter((y) => !equal(x, y)));
const nfix = (n) => (Number.isInteger(n) && n >= 0 ? n : 0);

// ---- messages
const marker = (sid) => cons(':marker', sid);
const markerp = (m) => consp(m) && car(m) === ':marker';
const markerSid = (m) => cdr(m);

// ---- concrete application/topology (the attachments of reviews/04-...-exp1-eval.lsp)
const APP = {
  'app-compute': (p, ls) => ({ l1: 'a1', l2: 'a2', a1: 'b1' }[ls] || ls),
  'app-receive': (p, j, m, ls) => [':rcv', p, j, m, ls],
  'app-send-p': (p, k, ls) => ls === 'a1' || ls === 'a2',
  'app-make-msg': (p, k, ls) => (p === 1 ? 'm1' : 'm2'),
  'in-nbrs': (p) => (p === 1 ? [2] : [1]),
  'out-nbrs': (p) => (p === 1 ? [2] : [1]),
  'init-local': (p) => (p === 1 ? 'l1' : 'l2'),
  'sys-procs': () => [1, 2],
};

// ---- accessors
const psOf = (p, st) => g(p, g(':pstates', st));
const sidsOf = (p, st) => g(':sids', psOf(p, st));
const outsOf = (p, st) => g(':out', psOf(p, st));
const insOf = (p, st) => g(':in', psOf(p, st));
const chanOf = (a, b, st) => g(new Pair(a, b), g(':chans', st));
const inProc = (x) => car(x), inType = (x) => car(cdr(x)), inSender = (x) => car(cdr(cdr(x)));
const recvP = (x) => inType(x) === ':receive';

// ---- local transitions
function markerOutbox(outs, sid) { return norm(listOf(outs).map((o) => new Pair(o, marker(sid)))); }
function appOutbox(p, outs, ls) {
  return norm(listOf(outs).filter((o) => APP['app-send-p'](p, o, ls))
    .map((o) => new Pair(o, APP['app-make-msg'](p, o, ls))));
}
function newEntry(ls, expect, chans) {
  return s(':state', ls, s(':chans', chans, s(':expect', expect,
    s(':status', consp(expect) ? ':checkpointing' : ':done', null))));
}
function recordMsg(sids, snaps, j, msg) {
  for (const sid of listOf(sids)) {
    const e = g(sid, snaps);
    if (g(':status', e) === ':checkpointing' && memberEqual(j, g(':expect', e))) {
      const ch = g(':chans', e);
      snaps = s(sid, s(':chans', s(j, [...listOf(g(j, ch)), msg], ch), e), snaps);
    }
  }
  return snaps;
}
function localPs(x, pso, head) {
  const p = inProc(x), j = inSender(x), app = g(':app', pso), sids = g(':sids', pso), snaps = g(':snaps', pso);
  switch (inType(x)) {
    case ':compute': return s(':app', APP['app-compute'](p, app), pso);
    case ':checkpoint': {
      const sid = new Pair(p, nfix(g(':counter', pso)));
      return s(':counter', 1 + nfix(g(':counter', pso)), s(':sids', cons(sid, sids),
        s(':snaps', s(sid, newEntry(app, g(':in', pso), null), snaps), pso)));
    }
    case ':receive': {
      if (markerp(head)) {
        const sid = markerSid(head);
        if (memberEqual(sid, sids)) {                       // later marker: close channel j
          const e = g(sid, snaps), ex = removeEqual(j, g(':expect', e));
          return s(':snaps', s(sid, s(':expect', ex, s(':status', consp(ex) ? g(':status', e) : ':done', e)), snaps), pso);
        }
        return s(':sids', cons(sid, sids),                // first marker: record local state
          s(':snaps', s(sid, newEntry(app, removeEqual(j, g(':in', pso)), s(j, null, null)), snaps), pso));
      }
      return s(':app', APP['app-receive'](p, j, head, app), s(':snaps', recordMsg(sids, snaps, j, head), pso));
    }
    default: return pso;
  }
}
function localOut(x, pso, head) {
  const p = inProc(x), sids = g(':sids', pso), outs = g(':out', pso);
  switch (inType(x)) {
    case ':compute': return appOutbox(p, outs, APP['app-compute'](p, g(':app', pso)));
    case ':checkpoint': return markerOutbox(outs, new Pair(p, nfix(g(':counter', pso))));
    case ':receive': return markerp(head) && !memberEqual(markerSid(head), sids) ? markerOutbox(outs, markerSid(head)) : null;
    default: return null;
  }
}

// ---- global transitions
const headOf = (st, x) => (recvP(x) ? car(chanOf(inSender(x), inProc(x), st)) : null);
function popChans(st, x) {
  const c = g(':chans', st);
  if (!recvP(x)) return c;
  const k = new Pair(inSender(x), inProc(x));
  return s(k, cdr(g(k, c)), c);
}
function deliver(p, ob, c) {
  for (const o of listOf(ob)) { const k = new Pair(p, o.car); c = s(k, [...listOf(g(k, c)), o.cdr], c); }
  return c;
}
function clStep(st, x) {
  const p = inProc(x);
  return s(':pstates', s(p, localPs(x, psOf(p, st), headOf(st, x)), g(':pstates', st)),
    s(':chans', deliver(p, localOut(x, psOf(p, st), headOf(st, x)), popChans(st, x)), st));
}
const clRun = (st, e) => e.reduce(clStep, st);

function legalInput(st, x) {
  return memberEqual(inProc(x), g(':procs', st)) &&
    [':compute', ':checkpoint', ':receive'].includes(inType(x)) &&
    (!recvP(x) || (memberEqual(inSender(x), g(':procs', st)) &&
      memberEqual(inSender(x), insOf(inProc(x), st)) && consp(chanOf(inSender(x), inProc(x), st))));
}
function legalExec(st, e) { for (const x of e) { if (!legalInput(st, x)) return false; st = clStep(st, x); } return true; }

// ---- initial state
function initPstates(ps) {
  let r = null;
  for (const p of [...listOf(ps)].reverse())
    r = s(p, s(':app', APP['init-local'](p), s(':in', APP['in-nbrs'](p), s(':out', APP['out-nbrs'](p),
      s(':sids', null, s(':counter', 0, s(':snaps', null, null)))))), r);
  return r;
}
const initState = () => s(':procs', APP['sys-procs'](), s(':pstates', initPstates(APP['sys-procs']()), s(':chans', null, null)));

// ---- snapshots, cut, segment
const recordedP = (sid, p, st) => memberEqual(sid, sidsOf(p, st));
function snapshotDoneAll(sid, ps, st) {
  return listOf(ps).every((p) => memberEqual(sid, sidsOf(p, st)) && g(':status', g(sid, g(':snaps', psOf(p, st)))) === ':done');
}
const checkpointComplete = (sid, st) => snapshotDoneAll(sid, g(':procs', st), st);
const segmentTarget = (st, e) => new Pair(inProc(e[0]), nfix(g(':counter', psOf(inProc(e[0]), st))));
function incompleteBeforeEach(sid, st, e) {
  for (const x of e) { if (checkpointComplete(sid, st)) return false; st = clStep(st, x); }
  return true;
}
function completeSegmentP(st, e) {
  return e.length > 0 && inType(e[0]) === ':checkpoint' && legalExec(st, e) &&
    incompleteBeforeEach(segmentTarget(st, e), st, e) && checkpointComplete(segmentTarget(st, e), clRun(st, e));
}
// pre/post classification: by recorded-p in the state *before* the input
function classify(sid, st, e) {
  const out = [];
  for (const x of e) { out.push(recordedP(sid, inProc(x), st) ? 'post' : 'pre'); st = clStep(st, x); }
  return out;
}
const preInputs = (sid, st, e) => { const c = classify(sid, st, e); return e.filter((_, i) => c[i] === 'pre'); };
const postInputs = (sid, st, e) => { const c = classify(sid, st, e); return e.filter((_, i) => c[i] === 'post'); };

function pstatesEquiv(ps, s1, s2) {
  return listOf(ps).every((p) => [':app', ':in', ':out', ':counter', ':sids'].every((f) => equal(g(f, psOf(p, s1)), g(f, psOf(p, s2)))));
}
const stateEquiv = (s1, s2) => equal(g(':procs', s1), g(':procs', s2)) && equal(g(':chans', s1), g(':chans', s2)) &&
  pstatesEquiv(g(':procs', s1), s1, s2);

// ---- emit an ACL2 term that builds the same object (used to check this port against ACL2)
function toAcl2(x) {
  if (x === null) return 'nil';
  if (typeof x === 'number') return String(x);
  if (typeof x === 'string') return x.startsWith(':') ? x : `'${x}`;
  if (x instanceof Pair) return `(cons ${toAcl2(x.car)} ${toAcl2(x.cdr)})`;
  if (Array.isArray(x)) return x.length ? `(list ${x.map(toAcl2).join(' ')})` : 'nil';
  if (x instanceof Rec) {
    let t = 'nil';
    for (const [k, v] of [...x.m.values()].reverse()) t = `(s ${toAcl2(k)} ${toAcl2(v)} ${t})`;
    return t;
  }
}

const MODEL = { Pair, Rec, cons, car, cdr, consp, listOf, show, equal, g, s, marker, markerp, markerSid, APP,
  psOf, sidsOf, outsOf, insOf, chanOf, inProc, inType, inSender, recvP, localPs, localOut, headOf, popChans,
  deliver, clStep, clRun, legalInput, legalExec, initState, recordedP, checkpointComplete, segmentTarget,
  completeSegmentP, classify, preInputs, postInputs, stateEquiv, recordMsg, toAcl2 };
if (typeof module !== 'undefined') module.exports = MODEL;
