#!/usr/bin/env python3
"""Grader for fw-ftc-macro (written before any run).  Usage: grade.sh <work-dir>

Requirements (prompt numbering):
 R1 the macro is /work/def-ftc-integral.lisp  -> grader books grade-r1-*.lisp (hidden calls with our own
    integrands, checks of the generated events against the specification, must-fails) + MANUAL check that a
    failed obligation is printed (log saved for the human);
 R2 /work/tests.lisp has calls (a)-(e), each followed by a check  -> tests.lisp is parsed, calls are
    identified (numerically / by symbol), and generated grade-r2-<x>.lisp books prove the closed form at
    concrete endpoints from the model's int-NAME-ftc;
 R3 both books certify with cert.pl --acl2 acl2r.
"""
import os, re, shutil, subprocess, sys, tempfile
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ACL2 = os.environ.get("GRADER_ACL2R", "/opt/acl2r/saved_acl2r")
CERT = os.environ.get("GRADER_CERT", "/opt/acl2r/books/build/cert.pl")
BANNED = (r"skip-proofs|defaxiom|defttag|set-ld-redefinition-action|skip-proofs-okp|:ttags|set-skip-proofs|"
          r"trust-tag|define-trusted-clause-processor|defun-unsound|sys-call|reset-prehistory|\bredef\b|set-cbd|"
          r"progn!|defattach-system|set-raw-mode|\bdefstobj\b.*:congruent-to|remove-untouchable|push-untouchable|"
          r"set-temp-touchable|with-raw-mode|include-raw")

# ---------------------------------------------------------------- s-expressions (from check-prove.py)
def tokens(s):
    s = re.sub(r"#\|.*?\|#", " ", s, flags=re.S)
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c == ";":
            j = s.find("\n", i); i = len(s) if j < 0 else j
        elif c.isspace():
            i += 1
        elif c in "()'`,":
            out.append(c); i += 1
        elif c == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(s[i:j + 1]); i = j + 1
        elif c == "|":
            j = s.find("|", i + 1); out.append(s[i:j + 1]); i = j + 1
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] not in "();\"'`,":
                j += 1
            out.append(s[i:j].lower()); i = j
    return out

def parse(toks):
    def rd(i):
        t = toks[i]
        if t == "(":
            lst, i = [], i + 1
            while toks[i] != ")":
                x, i = rd(i); lst.append(x)
            return lst, i + 1
        if t in ("'", "`", ","):
            x, i = rd(i + 1); return [{"'": "quote", "`": "quasiquote", ",": "unquote"}[t], x], i
        return t, i + 1
    forms, i = [], 0
    while i < len(toks):
        f, i = rd(i); forms.append(f)
    return forms

def unparse(x):
    if isinstance(x, list):
        if len(x) == 2 and x[0] == "quote": return "'" + unparse(x[1])
        return "(" + " ".join(unparse(y) for y in x) + ")"
    return x

def mentions(x, sym):
    if isinstance(x, list): return any(mentions(y, sym) for y in x)
    return x == sym or x.endswith("::" + sym)

# ---------------------------------------------------------------- numeric evaluation of unary integrands
class NoEval(Exception): pass

def num(tok):
    t = tok.lstrip("+")
    if re.fullmatch(r"-?\d+", t): return Fraction(int(t))
    if re.fullmatch(r"-?\d+/\d+", t): return Fraction(t)
    m = re.fullmatch(r"#x([0-9a-f]+)", t)
    if m: return Fraction(int(m.group(1), 16))
    raise NoEval(tok)

def ev(t, env):
    if isinstance(t, str):
        if t in env: return env[t]
        return num(t)
    if not t: raise NoEval("()")
    op, args = t[0], t[1:]
    if op == "quote": return num(t[1])
    if isinstance(op, list) and op and op[0] == "lambda":
        return ev(op[2], dict(zip(op[1], [ev(a, env) for a in args])))
    v = [ev(a, env) for a in args]
    if op in ("*", "binary-*"):
        r = Fraction(1)
        for a in v: r *= a
        return r
    if op in ("+", "binary-+"): return sum(v, Fraction(0))
    if op in ("-",):
        return -v[0] if len(v) == 1 else v[0] - sum(v[1:], Fraction(0))
    if op == "unary--": return -v[0]
    if op in ("/",):
        if len(v) == 1: return 1 / v[0]
        r = v[0]
        for a in v[1:]: r /= a
        return r
    if op == "unary-/": return 1 / v[0]
    if op == "expt" and v[1].denominator == 1: return v[0] ** int(v[1])
    if op in ("square", "sqr"): return v[0] * v[0]
    raise NoEval(op)

DEFS = {}  # unary defuns of tests.lisp: name -> (lambda (v) body)

def fn_value(spec, x):
    """value of a unary function spec (symbol or (lambda (v) body)) at x, or raise NoEval"""
    if isinstance(spec, str) and spec in DEFS:
        spec = DEFS[spec]
    if isinstance(spec, list) and spec and spec[0] == "lambda" and len(spec) == 3 and len(spec[1]) == 1:
        return ev(spec[2], {spec[1][0]: Fraction(x)})
    raise NoEval(str(spec))

def is_fn(spec, sym):
    """spec is the symbol sym or (lambda (v) (sym v))"""
    if spec == sym or spec == "acl2::" + sym: return True
    return (isinstance(spec, list) and len(spec) == 3 and spec[0] == "lambda" and len(spec[1]) == 1
            and spec[2] in ([sym, spec[1][0]], ["acl2::" + sym, spec[1][0]]))

def matches(spec, f, pts):
    try:
        return all(fn_value(spec, x) == f(Fraction(x)) for x in pts)
    except (NoEval, ZeroDivisionError, IndexError):
        return False

# ---------------------------------------------------------------- shared steps
def sh(cmd, cwd, log, timeout):
    with open(log, "w") as fh:
        try:
            r = subprocess.run(cmd, cwd=cwd, stdout=fh, stderr=subprocess.STDOUT, timeout=timeout)
            return r.returncode
        except subprocess.TimeoutExpired:
            fh.write("\nGRADER: TIMEOUT\n"); return 124

def certify(d, book, timeout=4 * 3600):
    log = os.path.join(d, "grader-logs", book.replace("/", "_") + ".log")
    os.makedirs(os.path.dirname(log), exist_ok=True)
    rc = sh(["perl", CERT, "--acl2", ACL2, book], d, log, timeout)
    ok = rc == 0 and os.path.exists(os.path.join(d, book + ".cert"))
    return ok, log

def reason(book_dir, book, log):
    out = os.path.join(book_dir, book + ".cert.out")
    txt = open(out, errors="replace").read() if os.path.exists(out) else open(log, errors="replace").read()
    m = re.search(r"GRADER-FAIL:(.*?)(\n\n|$)", txt, re.S)
    if m: return " ".join(m.group(1).split())[:400]
    m = re.search(r"ACL2 Error[^\n]*in ([^\n]*)", txt)
    return ("ACL2 error in " + " ".join(m.group(1).split())[:200]) if m else "did not certify"

def banned_scan(d):
    hits = []
    for root, _, files in os.walk(d):
        for fn in files:
            if fn.endswith((".lisp", ".lsp", ".acl2")) and fn != "acl2-customization.lsp":  # not read by cert.pl
                p = os.path.join(root, fn)
                src = open(p, errors="replace").read()
                # cert.pl reads "; cert-flags:" / "cert_param:" comments, so check those before stripping comments
                m = re.search(r"cert[-_](?:flags|param)[^\n]*(?:skip-proofs|ttags|acl2x)", src, re.I)
                if m: hits.append(f"{os.path.relpath(p, d)}: {m.group(0)}")
                code = re.sub(r";[^\n]*", "", re.sub(r"#\|.*?\|#", " ", src, flags=re.S))
                m = re.search(BANNED, code, re.I)
                if m: hits.append(f"{os.path.relpath(p, d)}: {m.group(0)}")
    return hits

# ---------------------------------------------------------------- main
def main():
    work = sys.argv[1]
    tmp = tempfile.mkdtemp(prefix="grade-fw-ftc-macro-")
    d = os.path.join(tmp, "work")
    shutil.copytree(work, d, symlinks=False, ignore=shutil.ignore_patterns(".git", "*.cert", "*.fasl", "*.port",
                                                                           "*.cert.out", ".sys"))
    print(f"GRADER: work copy in {d}")
    res = {}
    absw = [f for f in os.listdir(d) if f.endswith((".lisp", ".acl2"))
            and re.search(r'"/work/', open(os.path.join(d, f), errors="replace").read())]
    if absw:
        print(f"GRADER: WARNING absolute /work paths in {absw}; they resolve outside the copy")
    hits = banned_scan(d)
    if hits:
        for r in (1, 2, 3):
            res[r] = ("FAIL", "banned event: " + "; ".join(hits))
        report(res); return
    have_macro = os.path.exists(os.path.join(d, "def-ftc-integral.lisp"))
    have_tests = os.path.exists(os.path.join(d, "tests.lisp"))
    # R3: certification of both books
    okm, logm = certify(d, "def-ftc-integral") if have_macro else (False, None)
    okt, logt = certify(d, "tests") if have_tests else (False, None)
    if okm and okt:
        res[3] = ("PASS", "")
    else:
        why = []
        if not have_macro: why.append("def-ftc-integral.lisp missing")
        elif not okm: why.append("def-ftc-integral: " + reason(d, "def-ftc-integral", logm))
        if not have_tests: why.append("tests.lisp missing")
        elif not okt: why.append("tests: " + reason(d, "tests", logt))
        res[3] = ("FAIL", "; ".join(why))
    # R1: hidden tests
    if not okm:
        res[1] = ("FAIL", "def-ftc-integral.lisp missing or does not certify")
    else:
        fails = []
        for b in ("grade-r1-lin", "grade-r1-exp", "grade-r1-sym", "grade-r1-fail"):
            shutil.copy(os.path.join(HERE, b + ".lisp"), d)
        shutil.copy(os.path.join(HERE, "grader-ftc-lib.lisp"), d)
        for b in ("grade-r1-lin", "grade-r1-exp", "grade-r1-sym", "grade-r1-fail"):
            ok, log = certify(d, b)
            print(f"  R1/{b} {'PASS' if ok else 'FAIL ' + reason(d, b, log)}")
            if not ok: fails.append(b)
        # log of a failing call, for the manual check of the error message
        errlog = os.path.join(d, "grader-logs", "r1-failed-call.log")
        script = os.path.join(d, "grader-logs", "r1-failed-call.lsp")
        with open(script, "w") as fh:
            fh.write('(include-book "nonstd/integrals/ftc-2" :dir :system)\n(include-book "def-ftc-integral")\n'
                     "(def-ftc-integral gr-bad1 :integrand (lambda (x) (* 2 x))"
                     " :antiderivative (lambda (x) (* x x x)) :domain (interval nil nil))\n")
        with open(script) as fin, open(errlog, "w") as fout:
            try:
                subprocess.run([ACL2], cwd=d, stdin=fin, stdout=fout, stderr=subprocess.STDOUT, timeout=3600)
            except subprocess.TimeoutExpired:
                fout.write("\nGRADER: TIMEOUT\n")
        if fails:
            res[1] = ("FAIL", "hidden checks failed: " + ", ".join(fails))
        else:
            res[1] = ("MANUAL", f"mechanical checks passed; inspect {errlog} (CHECKLIST R1-M: the failed call "
                                "must stop with an error that prints the derivative obligation)")
    # R2: the calls in tests.lisp
    res[2] = grade_r2(d, have_tests, okt)
    report(res)

def collect_calls(forms):
    """(call, in_must_fail, sibling_index, siblings) for every def-ftc-integral form"""
    out = []
    def walk(f, sibs, idx, mf):
        if not isinstance(f, list) or not f: return
        h = f[0].split("::")[-1] if isinstance(f[0], str) else None
        if h == "def-ftc-integral":
            out.append((f, mf, idx, sibs)); return
        if h in ("must-fail", "must-fail-local", "must-fail!", "must-fail-with-error", "must-fail-with-soft-error",
                 "must-fail-with-hard-error"):
            for g in f[1:]: walk(g, sibs, idx, True)
            return
        if h in ("local", "progn", "encapsulate", "defsection", "with-output", "must-succeed"):
            for g in f[1:]:
                walk(g, sibs, idx, mf)
    for i, f in enumerate(forms):
        walk(f, forms, i, False)
    return out

def kwargs(call):
    kw, i = {}, 2
    while i + 1 < len(call):
        if isinstance(call[i], str) and call[i].startswith(":"):
            kw[call[i]] = call[i + 1]
        i += 2
    return kw

TARGETS = {
    # label: (integrand test, antiderivative test, domain, value check (a, b, expected) or None, no-theorems?)
    "a": (lambda s: matches(s, lambda x: x * x, [2, 3, 5]),
          lambda s: matches(s, lambda x: x ** 3 / 3, [2, 3, 5]), "(interval nil nil)", ("0", "3", "9"), True),
    "b": (lambda s: is_fn(s, "acl2-cosine"), lambda s: is_fn(s, "acl2-sine"), "(interval nil nil)",
          ("0", "1", "(- (acl2-sine 1) (acl2-sine 0))"), True),
    "c": (lambda s: matches(s, lambda x: 1 / (x * x), [2, 3, 5]),
          lambda s: matches(s, lambda x: -1 / x, [2, 3, 5]), "(interval 1 nil)", ("1", "2", "1/2"), True),
    "d": (lambda s: is_fn(s, "acl2-ln"), lambda s: mentions(s, "acl2-ln") or isinstance(s, str), "(interval 1 nil)",
          ("1", "2", "(- (- (* 2 (acl2-ln 2)) 2) (- (* 1 (acl2-ln 1)) 1))"), False),
}

def grade_r2(d, have_tests, okt):
    if not have_tests:
        return ("FAIL", "tests.lisp missing")
    if not okt:
        return ("FAIL", "tests.lisp does not certify")
    src = open(os.path.join(d, "tests.lisp"), errors="replace").read()
    try:
        forms = parse(tokens(src))
    except Exception as e:
        return ("FAIL", f"cannot parse tests.lisp: {e}")
    if not any(isinstance(f, list) and len(f) >= 2 and f[0] == "include-book"
               and f[1].strip('"').endswith("def-ftc-integral") for f in
               [g[1] if isinstance(g, list) and g[:1] == ["local"] else g for g in forms]):
        return ("FAIL", "tests.lisp does not include def-ftc-integral")
    def defs(f):
        if isinstance(f, list) and f and f[0] in ("local", "progn", "encapsulate", "defsection"):
            for g in f[1:]: defs(g)
        elif (isinstance(f, list) and len(f) >= 4 and f[0] in ("defun", "defund") and isinstance(f[2], list)
              and len(f[2]) == 1):
            DEFS[f[1]] = ["lambda", f[2], f[-1]]
    for f in forms: defs(f)
    calls = collect_calls(forms)
    probs, manual = [], []
    for lab, (fi, fa, dom, val, nothm) in TARGETS.items():
        cands = [c for c in calls if not c[1] and isinstance(c[0][1], str)
                 and fi(kwargs(c[0]).get(":integrand")) and fa(kwargs(c[0]).get(":antiderivative"))]
        if not cands:
            probs.append(f"({lab}) no matching call"); continue
        call, _, idx, sibs = cands[0]
        name, kw = call[1].split("::")[-1], kwargs(call)
        if nothm and (":derivative-thm" in kw or ":continuity-thm" in kw):
            probs.append(f"({lab}) {name}: theorems supplied"); continue
        # the model's own check after the call: a later form, before the next call, mentions int-NAME(-ftc)
        nxt = [c[2] for c in calls if c[3] is sibs and c[2] > idx]
        stop = min(nxt) if nxt else len(sibs)
        if not any(mentions(sibs[j], f"int-{name}-ftc") or mentions(sibs[j], f"int-{name}")
                   for j in range(idx + 1, stop)):
            probs.append(f"({lab}) {name}: no check of int-{name}-ftc after the call")
        # our own check, in ACL2
        a, b, expv = val
        book = f"grade-r2-{lab}"
        idcheck = ""
        if lab == "d":
            idcheck = (f"(defthm grader-r2-d-antiderivative\n  (implies (and (realp x) (< 0 x))\n"
                       f"           (equal {unparse([kw[':antiderivative'], 'x'])} (- (* x (acl2-ln x)) x)))\n"
                       f"  :rule-classes nil)\n\n")
        with open(os.path.join(d, book + ".lisp"), "w") as fh:
            fh.write(f"""; Grader R2({lab}), generated by grade.py from the call {name} in tests.lisp
(in-package "ACL2")
(include-book "tests")
(local (include-book "arithmetic/top" :dir :system))

(assert-event (equal {unparse(kw.get(':domain', 'nil'))} {dom}))

{idcheck}(defthm grader-r2-{lab}-value
  (equal (int-{name} {a} {b}) {expv})
  :hints (("Goal" :use ((:instance int-{name}-ftc (a {a}) (b {b})))
           :in-theory (e/d (inside-interval-p interval (:e inside-interval-p) (:e interval))
                           (int-{name} (:e int-{name}) strict-int-{name} (:e strict-int-{name}))))))
""")
        ok, log = certify(d, book)
        print(f"  R2/{lab} call {name}: {'PASS' if ok else 'FAIL ' + reason(d, book, log)}")
        if not ok: probs.append(f"({lab}) {name}: grader check failed")
    # (e): a must-fail call with a wrong antiderivative
    mfs = [c for c in calls if c[1]]
    if not mfs:
        probs.append("(e) no def-ftc-integral inside must-fail")
    else:
        wrong = None
        for call, *_ in mfs:
            kw = kwargs(call)
            fi, fa = kw.get(":integrand"), kw.get(":antiderivative")
            try:
                h = Fraction(1, 10 ** 6)
                diffs = [abs((fn_value(fa, x + h) - fn_value(fa, x)) / h - fn_value(fi, x)) for x in (2, 3, 5)]
                if max(diffs) > Fraction(1, 100): wrong = call[1]; break
            except (NoEval, ZeroDivisionError):
                manual.append(f"(e) cannot evaluate {unparse(fi)} / {unparse(fa)} in {call[1]}")
        if wrong:
            print(f"  R2/e must-fail call {wrong}: antiderivative numerically wrong: PASS")
        elif not manual:
            probs.append("(e) the must-fail calls have numerically correct antiderivatives")
    if probs:
        return ("FAIL", "; ".join(probs))
    if manual:
        return ("MANUAL", "; ".join(manual) + " (CHECKLIST R2-e: confirm the antiderivative is wrong)")
    return ("PASS", "")

def report(res):
    allok = True
    for r in (1, 2, 3):
        st, why = res.get(r, ("FAIL", "not checked"))
        print(f"R{r} {st}" + (f" {why}" if why else ""))
        if st == "FAIL": allok = False
    n = {s: sum(1 for v in res.values() if v[0] == s) for s in ("PASS", "FAIL", "MANUAL")}
    print(f"SUMMARY fw-ftc-macro: {n['PASS']} PASS, {n['FAIL']} FAIL, {n['MANUAL']} MANUAL")
    sys.exit(0 if allok else 1)

if __name__ == "__main__":
    main()
