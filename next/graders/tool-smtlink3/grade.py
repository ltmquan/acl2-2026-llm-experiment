#!/usr/bin/env python3
"""Grader for tool-smtlink3 (ACL2 8.7, paper chen-smtlink3).

Usage: python3 -I grade.py <work-dir>      (grade.sh is a thin wrapper)

Prints one line per requirement of next/tasks/tool-smtlink3/prompt.txt:
  R<n> PASS | R<n> FAIL <reason> | R<n> MANUAL <what to inspect (see CHECKLIST.md)>
then a SUMMARY line.  Exit 0 iff no requirement FAILs and no banned event was found.

Steps
 1. copy <work-dir> to a fresh temp dir (stale .cert/.port/compiled files are not copied);
 2. scan the model's .lisp/.lsp/.acl2 files: banned events anywhere (skip-proofs, defaxiom,
    redefinition, ...); trust-tag machinery (defttag, define-trusted-clause-processor, sys-call*,
    progn!, set-raw-mode, include-raw, trust-tag) only in the book F that contains the one
    define-trusted-clause-processor and in the model's books that F includes (transitively);
    `:ttags` is allowed only as an include-book argument outside those books; cert-flags may add
    :ttags but not :skip-proofs-okp / :defaxioms-okp;
 3. give every model book cert-flags that allow ttags (`? t :ttags :all`, unless the model already
    gave a :ttags list), then certify every model .lisp file with cert.pl, with a logging `z3`
    wrapper first on PATH (it records each solver call's input and output);
 4. copy books/ to <copy>/grader/ and certify the grader books against the model's books:
    grade-r3, grade-r4, grade-r6, grade-r7 with the logging wrapper (real Z3), grade-r3-unknown
    with a fake z3 that answers `unknown`, grade-r3-error with a fake z3 that prints an error and
    exits 1;
 5. R2 world check: in an ACL2 session include F alone, then smtlink and examples; list trusted
    clause processors, verified clause-processor rules and ttags-seen;
 6. structural checks of examples.lisp (the model's own examples of R4-R7).
"""
import os, re, shutil, subprocess, sys, tempfile, glob, itertools
from fractions import Fraction

ACL2 = "/opt/acl2/saved_acl2"
CERT = "/opt/acl2/books/build/cert.pl"
HERE = os.path.dirname(os.path.abspath(__file__))
JOBS = str(max(1, min(8, os.cpu_count() or 1)))
MODEL_TIMEOUT = 4 * 3600
BOOK_TIMEOUT = 3600

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
            if c == "," and i + 1 < len(s) and s[i + 1] == "@":
                out.append(",@"); i += 2; continue
            out.append(c); i += 1
        elif c == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(s[i:j + 1]); i = j + 1
        elif c == "|":
            j = s.find("|", i + 1)
            if j < 0: j = len(s) - 1
            out.append(s[i:j + 1]); i = j + 1
        elif c == "#" and i + 1 < len(s) and s[i + 1] in "\\":
            out.append(s[i:i + 3].lower()); i += 3
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
            while i < len(toks) and toks[i] != ")":
                x, i = rd(i); lst.append(x)
            return lst, i + 1
        if t in ("'", "`", ",", ",@"):
            x, i = rd(i + 1)
            return [{"'": "quote", "`": "quasiquote", ",": "unquote", ",@": "unquote"}[t], x], i
        return t, i + 1
    forms, i = [], 0
    while i < len(toks):
        if toks[i] == ")":
            i += 1; continue
        f, i = rd(i); forms.append(f)
    return forms

def read_forms(path):
    try:
        return parse(tokens(open(path, errors="replace").read()))
    except Exception:
        return []

def unpkg(x):
    if isinstance(x, str):
        if x.startswith('"') or x.startswith("|"): return x
        return re.sub(r"^[^:]*::?(?=.)", "", x) if "::" in x else x
    return [unpkg(y) for y in x]

def walk(x, fn, ctx=()):
    """Call fn(form, ctx) on every list sub-form; ctx = tuple of enclosing heads."""
    if isinstance(x, list):
        fn(x, ctx)
        head = x[0] if x and isinstance(x[0], str) else None
        for y in x:
            walk(y, fn, ctx + ((head,) if head else ()))

# ---------------------------------------------------------------- banned events
BANNED_ANY = {"skip-proofs", "defaxiom", "set-ld-redefinition-action", "redef", "redef!", "redef+",
              "redef-", "set-skip-proofs", "skip-proofs-okp", "defun-unsound", "reset-prehistory",
              "defattach-system", "set-raw-proof-format", "with-redef", "set-skip-proofs-okp"}
TTAG_TOKENS = {"defttag", "define-trusted-clause-processor", "progn!", "set-raw-mode",
               "set-raw-mode-on", "set-raw-mode-on!", "include-raw", "trust-tag", "remove-untouchable",
               "push-untouchable", "defmacro-last", "return-last-table", "set-temp-touchable-fns",
               "set-temp-touchable-vars", "defun-overrides", "open-trace-file!", "with-raw-mode"}

def is_ttag_token(t):
    t = unpkg(t)
    return t in TTAG_TOKENS or t.startswith("sys-call")

def sub_lists(x):
    """All list sub-forms, not descending into defpkg forms (their import lists are just symbols)."""
    if isinstance(x, list):
        if x and isinstance(x[0], str) and unpkg(x[0]) == "defpkg": return
        yield x
        for y in x: yield from sub_lists(y)

def atoms_outside_defpkg(x):
    if isinstance(x, list):
        if x and isinstance(x[0], str) and unpkg(x[0]) == "defpkg": return
        for y in x: yield from atoms_outside_defpkg(y)
    elif isinstance(x, str) and not x.startswith('"'):
        yield x

def model_files(root):
    out = []
    for dp, dns, fns in os.walk(root):
        dns[:] = [d for d in dns if d not in (".git", "grader")]
        for f in fns:
            if f.endswith((".lisp", ".lsp", ".acl2")):
                out.append(os.path.join(dp, f))
    return sorted(out)

def local_includes(path, forms):
    """Model-local books included (include-book without :dir) by the file, as absolute .lisp paths."""
    res = []
    def fn(f, ctx):
        if f and unpkg(f[0]) == "include-book" and len(f) > 1 and isinstance(f[1], str) \
           and f[1].startswith('"') and ":dir" not in f:
            p = os.path.normpath(os.path.join(os.path.dirname(path), f[1].strip('"') + ".lisp"))
            if os.path.exists(p): res.append(p)
    for f in forms: walk(f, fn)
    return res

def scan(root):
    """Returns (banned_msgs, trusted_files, allowed_files)."""
    files = model_files(root)
    forms = {p: read_forms(p) for p in files}
    banned = []
    trusted_files = []
    for p, fs in forms.items():
        n = sum(1 for f in fs for g in sub_lists(f) if g and isinstance(g[0], str)
                and unpkg(g[0]) == "define-trusted-clause-processor")
        if n: trusted_files.append((p, n))
    allowed = set()
    if len(trusted_files) == 1 and trusted_files[0][1] == 1:
        todo = [trusted_files[0][0]]
        while todo:
            p = todo.pop()
            if p in allowed: continue
            allowed.add(p)
            todo += local_includes(p, forms.get(p, read_forms(p)))
    for p in files:
        src = open(p, errors="replace").read()
        rel = os.path.relpath(p, root)
        toks = [t for f in forms[p] for t in atoms_outside_defpkg(f)]
        for t in toks:
            u = unpkg(t)
            if u in BANNED_ANY:
                banned.append(f"{rel}: {u}")
            if is_ttag_token(t) and p not in allowed:
                banned.append(f"{rel}: {u} outside the trusted clause processor's book(s)")
        # :ttags outside allowed books only as an include-book argument
        if p not in allowed:
            cnt_all = sum(1 for t in toks if unpkg(t) == ":ttags")
            cnt_inc = [0]
            def fn(f, ctx):
                if f and isinstance(f[0], str) and unpkg(f[0]) == "include-book":
                    cnt_inc[0] += sum(1 for y in f if y == ":ttags")
            for f in forms[p]: walk(f, fn)
            if cnt_all > cnt_inc[0]:
                banned.append(f"{rel}: :ttags other than as an include-book argument outside the "
                              "trusted clause processor's book(s)")
        if p.endswith(".acl2"):
            for line in src.splitlines():
                m = re.match(r"^[ \t]*;[; \t]*cert-flags:(.*)$", line)
                if m and re.search(r":(skip-proofs-okp|defaxioms-okp)\s+(?!nil\b)", m.group(1), re.I):
                    banned.append(f"{rel}: cert-flags allow skip-proofs/defaxioms")
    return banned, trusted_files, allowed

# ---------------------------------------------------------------- cert flags
FLAG_RE = re.compile(r"^([ \t]*;[; \t]*cert-flags:)(.*)$", re.M)

def ensure_ttag_flags(root):
    """Give every model book effective cert-flags that allow ttags."""
    for dp, dns, fns in os.walk(root):
        dns[:] = [d for d in dns if d not in (".git", "grader")]
        for f in fns:
            if not f.endswith(".lisp"): continue
            book = os.path.join(dp, f[:-5])
            own, dirc = book + ".acl2", os.path.join(dp, "cert.acl2")
            if os.path.exists(own):
                src = open(own).read()
            elif os.path.exists(dirc):
                src = open(dirc).read()
                m = FLAG_RE.search(src)
                if m and ":ttags" in m.group(2).lower(): continue
            else:
                src = ""
            m = FLAG_RE.search(src)
            if m:
                if ":ttags" in m.group(2).lower():
                    if not os.path.exists(own): open(own, "w").write(src)
                    continue
                src = src[:m.start()] + m.group(1) + m.group(2).rstrip() + " :ttags :all" + src[m.end():]
            else:
                src = src.rstrip("\n") + "\n; cert-flags: ? t :ttags :all\n"
            open(own, "w").write(src)

# ---------------------------------------------------------------- z3 wrappers
WRAP = r'''#!/bin/bash
# grader z3 wrapper, mode=@MODE@
LOG="${GRADER_Z3_LOG:-@DEFLOG@}"; mkdir -p "$LOG"; d=$(mktemp -d "$LOG/call-XXXXXX")
printf '%s\n' "$@" > "$d/args"
files=0
for a in "$@"; do if [ -f "$a" ]; then cat "$a" >> "$d/input.smt2"; files=1; fi; done
case "@MODE@" in
  real)
    if [ $files = 1 ]; then "@REAL@" "$@" | tee "$d/output"; exit ${PIPESTATUS[0]}
    else tee "$d/input.smt2" | "@REAL@" "$@" | tee "$d/output"; exit ${PIPESTATUS[1]}; fi ;;
  unknown)
    if [ $files = 0 ]; then timeout 5 cat > "$d/input.smt2"; fi
    echo unknown | tee "$d/output"; exit 0 ;;
  error)
    if [ $files = 0 ]; then timeout 5 cat > "$d/input.smt2"; fi
    echo '(error "grader: simulated solver failure")' | tee "$d/output"; exit 1 ;;
esac
'''

def make_wrappers(tmp, real):
    bins = {}
    for mode in ("real", "unknown", "error"):
        d = os.path.join(tmp, "bin-" + mode); os.makedirs(d)
        p = os.path.join(d, "z3")
        open(p, "w").write(WRAP.replace("@MODE@", mode).replace("@REAL@", real or "/nonexistent-z3")
                           .replace("@DEFLOG@", os.path.join(tmp, "z3log", "other")))
        os.chmod(p, 0o755)
        bins[mode] = d
    return bins

def z3_calls(logdir):
    out = []
    for d in sorted(glob.glob(os.path.join(logdir, "call-*"))):
        rd = lambda n: open(os.path.join(d, n), errors="replace").read() if os.path.exists(os.path.join(d, n)) else ""
        out.append({"dir": d, "input": rd("input.smt2"), "output": rd("output"), "args": rd("args")})
    return out

# ---------------------------------------------------------------- certification
def run_cert(cwd, targets, env, log, timeout):
    with open(log, "w") as fh:
        try:
            r = subprocess.run(["perl", CERT, "--acl2", ACL2, "-j", JOBS, "-k"] + targets, cwd=cwd,
                               stdout=fh, stderr=subprocess.STDOUT, timeout=timeout, env=env,
                               stdin=subprocess.DEVNULL)
            return r.returncode
        except subprocess.TimeoutExpired:
            fh.write("\nGRADER: TIMEOUT\n"); return -1

def certified(book):  # book path without extension
    return os.path.exists(book + ".cert")

# ---------------------------------------------------------------- structural checks on examples.lisp
def frac_norm(x):
    """Light normalization: strip packages, (/ a b) of literals -> a/b, real/rationalp -> rationalp."""
    x = unpkg(x)
    if isinstance(x, list):
        x = [frac_norm(y) for y in x]
        if len(x) == 3 and x[0] == "/" and all(isinstance(y, str) and re.fullmatch(r"-?\d+", y) for y in x[1:]):
            return str(Fraction(int(x[1]), int(x[2])))
        return x
    if x == "real/rationalp": return "rationalp"
    if re.fullmatch(r"-?\d+/\d+", x): return str(Fraction(x))
    return x

def defthms(forms):
    """All defthm-like forms anywhere: (name, formula, hints, in_must_fail)."""
    out = []
    def fn(f, ctx):
        if f and isinstance(f[0], str) and unpkg(f[0]) in ("defthm", "defthmd", "thm") and len(f) >= 2:
            if unpkg(f[0]) == "thm":
                name, formula, rest = None, f[1], f[2:]
            else:
                if len(f) < 3: return
                name, formula, rest = unpkg(f[1]), f[2], f[3:]
            hints = None
            for i in range(len(rest) - 1):
                if rest[i] == ":hints": hints = rest[i + 1]
            inmf = any(c and unpkg(c) in ("must-fail", "must-fail!", "must-fail-local") for c in ctx)
            out.append((name, frac_norm(formula), hints, inmf))
    for f in forms: walk(f, fn)
    return out

def flat(x):
    if isinstance(x, list):
        for y in x: yield from flat(y)
    else:
        yield x

def has_smtlink(h):
    return h is not None and ":smtlink" in [unpkg(t) if isinstance(t, str) else t for t in flat(h)]

PAPER_HYPS = frac_norm(parse(tokens("""((real/rationalp x) (real/rationalp y)
   (<= (+ (* (/ 9 8) x x) (* y y)) 1) (<= (x^2-y^2 x y) 1))"""))[0])
PAPER_CONCL = frac_norm(parse(tokens("(< y (- (* 3 (- x (/ 17 8)) (- x (/ 17 8))) 3))"))[0])
ALIST_GOAL = frac_norm(parse(tokens("""(implies (and (integerp k1) (integerp k2) (symbolp v1) (symbolp v2)
   (int-sym-alist-p al)) (equal (assoc-equal k1 (cons (cons k1 v1) (cons (cons k2 v2) al))) (cons k1 v1)))"""))[0])

def split_implies(f):
    if isinstance(f, list) and len(f) == 3 and f[0] == "implies":
        h = f[1]
        hyps = h[1:] if isinstance(h, list) and h and h[0] == "and" else [h]
        return hyps, f[2]
    return None, None

# tiny evaluator for the false-variant check (R5)
class Unsupported(Exception): pass

def ev(t, env):
    if isinstance(t, str):
        if re.fullmatch(r"-?\d+(/\d+)?", t): return Fraction(t)
        if t == "t": return True
        if t == "nil": return False
        if t in env: return env[t]
        raise Unsupported(t)
    if not t: raise Unsupported("()")
    op, args = t[0], t[1:]
    if op == "quote":
        if isinstance(args[0], str) and re.fullmatch(r"-?\d+(/\d+)?", args[0]): return Fraction(args[0])
        raise Unsupported("quote")
    if op == "implies": return (not ev(args[0], env)) or bool(ev(args[1], env))
    if op == "and": return all(ev(a, env) for a in args)
    if op == "or": return any(ev(a, env) for a in args)
    if op == "not": return not ev(args[0], env)
    if op == "if": return ev(args[1], env) if ev(args[0], env) else ev(args[2], env)
    v = [ev(a, env) for a in args]
    num = lambda a: a if isinstance(a, Fraction) else Fraction(0)
    if op in ("rationalp", "acl2-numberp", "real/rationalp"): return isinstance(v[0], Fraction)
    if op == "integerp": return isinstance(v[0], Fraction) and v[0].denominator == 1
    if op == "+": return sum((num(a) for a in v), Fraction(0))
    if op == "*":
        r = Fraction(1)
        for a in v: r *= num(a)
        return r
    if op == "-": return -num(v[0]) if len(v) == 1 else num(v[0]) - num(v[1])
    if op == "/":
        if len(v) == 1: return Fraction(0) if num(v[0]) == 0 else 1 / num(v[0])
        return Fraction(0) if num(v[1]) == 0 else num(v[0]) / num(v[1])
    if op == "<": return num(v[0]) < num(v[1])
    if op == "<=": return num(v[0]) <= num(v[1])
    if op == ">": return num(v[0]) > num(v[1])
    if op == ">=": return num(v[0]) >= num(v[1])
    if op in ("=", "equal"): return v[0] == v[1]
    if op == "/=": return v[0] != v[1]
    if op == "x^2-y^2": return num(v[0]) * num(v[0]) - num(v[1]) * num(v[1])
    if op == "expt" and v[1].denominator == 1 and v[1] >= 0: return num(v[0]) ** int(v[1])
    raise Unsupported(op)

def free_vars(t, acc):
    if isinstance(t, str):
        if not re.fullmatch(r"-?\d+(/\d+)?", t) and t not in ("t", "nil"): acc.add(t)
    elif t and t[0] != "quote":
        for a in t[1:]: free_vars(a, acc)
    return acc

def find_counterexample(formula):
    vs = sorted(free_vars(formula, set()))
    if not vs or len(vs) > 3: return None
    grid = [Fraction(k, 16) for k in range(-64, 65)] if len(vs) <= 2 else [Fraction(k, 4) for k in range(-16, 17)]
    try:
        for vals in itertools.product(grid, repeat=len(vs)):
            env = dict(zip(vs, vals))
            if not ev(formula, env): return env
    except Unsupported:
        return None
    return None

def structural(root):
    path = os.path.join(root, "examples.lisp")
    res = {}
    if not os.path.exists(path):
        for r in (4, 5, 6, 7): res[r] = (False, "examples.lisp missing")
        res["hyp"] = (False, "examples.lisp missing")
        return res
    ths = defthms(read_forms(path))
    proved = [t for t in ths if not t[3]]
    # R4
    main = [t for t in proved if t[0] == "poly-ineq-example"]
    perm = []
    ok_main = False
    for name, f, h, _ in main:
        hyps, concl = split_implies(f)
        if hyps == PAPER_HYPS and concl == PAPER_CONCL and has_smtlink(h): ok_main = True
    for name, f, h, _ in proved:
        hyps, concl = split_implies(f)
        if hyps and concl == PAPER_CONCL and hyps != PAPER_HYPS and len(hyps) == len(PAPER_HYPS) \
           and sorted(map(str, hyps)) == sorted(map(str, PAPER_HYPS)) and has_smtlink(h):
            perm.append(name)
    if not ok_main:
        res[4] = (False, "examples.lisp has no defthm poly-ineq-example with the paper's statement and an :smtlink hint")
    elif not perm:
        res[4] = (False, "examples.lisp has no :smtlink proof of poly-ineq-example with permuted hypotheses")
    else:
        res[4] = (True, "poly-ineq-example and permuted version(s) " + ", ".join(map(str, perm)))
    # R5
    mf = [t for t in ths if t[3] and has_smtlink(t[2]) and "x^2-y^2" in list(flat(t[1]))]
    if not mf:
        res[5] = (False, "no must-fail of an :smtlink defthm mentioning x^2-y^2 in examples.lisp")
    else:
        cex = [(t, find_counterexample(t[1])) for t in mf]
        good = [(t, c) for t, c in cex if c is not None and split_implies(t[1])[0] is not None]
        if good:
            t, c = good[0]
            res[5] = (True, f"must-fail {t[0]}: counterexample " + ", ".join(f"{k}={v}" for k, v in c.items()))
        else:
            res[5] = ("manual", "must-fail form(s) " + ", ".join(str(t[0]) for t in mf) +
                      " found but no counterexample on the grader's grid: inspect whether the goal is false")
    # R6
    terse = []
    for name, f, h, _ in proved:
        hyps, concl = split_implies(f)
        if hyps is None or not has_smtlink(h): continue
        if len(hyps) == 2 and hyps[0] == ["integerp", "y"] and hyps[1] in (["=", "x", ["*", "2", "y"]],
                                                                         ["equal", "x", ["*", "2", "y"]]) \
           and isinstance(concl, list) and len(concl) == 3 and concl[1:] == ["x", "y"] \
           and isinstance(concl[0], str):
            terse.append(name)
    hyp = [t[0] for t in proved if has_smtlink(t[2]) and ":hypothesize" in [unpkg(x) for x in flat(t[2]) if isinstance(x, str)]]
    res[6] = (bool(terse) and bool(hyp),
              ("type-terse " + ",".join(map(str, terse)) if terse else "no :smtlink defthm of the Section 4.1 shape "
               "(implies (and (integerp y) (= x (* 2 y))) (foo x y))") + "; " +
              ("hypothesize " + ",".join(map(str, hyp)) if hyp else "no proved defthm with :hypothesize in its :smtlink hint"))
    # R7
    al = []
    for name, f, h, _ in proved:
        if f != ALIST_GOAL or not has_smtlink(h): continue
        toks = [unpkg(x) for x in flat(h) if isinstance(x, str)]
        auto = all(isinstance(e, list) and len(e) == 3 and unpkg(e[1]) == ":smtlink" for e in (h if isinstance(h, list) else []))
        if "int-sym-top-down-translation-of-assoc-equal" in toks and "int-sym-top-down-translation-of-acons" in toks and auto:
            al.append(name)
    res[7] = (bool(al), ("alist goal proved by " + ",".join(map(str, al))) if al else
              "no defthm of the Section 5.7 goal whose only hints are :smtlink hints naming both "
              "int-sym-top-down-translation-of-assoc-equal and int-sym-top-down-translation-of-acons")
    return res

# ---------------------------------------------------------------- R2 world check
R2_SCRIPT = """(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(include-book "@F@" :ttags :all)
(assign grader-seen1 (global-val 'ttags-seen (w state)))
(assign grader-tr1 (strip-cars (table-alist 'trusted-cl-proc-table (w state))))
(include-book "smtlink" :ttags :all)
(include-book "examples" :ttags :all)
(defun grader-not-covered (seen2 seen1)
  (declare (xargs :mode :program))
  (cond ((endp seen2) nil)
        (t (let* ((tag (caar seen2)) (files2 (cdar seen2)) (files1 (cdr (assoc-eq tag seen1))))
             (append (if (subsetp-equal files2 files1) nil (list (cons tag (set-difference-equal files2 files1))))
                     (grader-not-covered (cdr seen2) seen1))))))
(cw "~%GRADER-TRUSTED1 ~x0~%" (remove1-eq 'proof-builder-cl-proc (@ grader-tr1)))
(cw "~%GRADER-TRUSTED2 ~x0~%" (remove1-eq 'proof-builder-cl-proc (strip-cars (table-alist 'trusted-cl-proc-table (w state)))))
(cw "~%GRADER-VERIFIED ~x0~%" (strip-cars (global-val 'clause-processor-rules (w state))))
(cw "~%GRADER-TTAGS ~x0~%" (global-val 'ttags-seen (w state)))
(cw "~%GRADER-TTAGS-NOT-VIA-F ~x0~%" (grader-not-covered (global-val 'ttags-seen (w state)) (@ grader-seen1)))
(cw "~%GRADER-R2-DONE~%")
"""

def r2_world(root, F, env, log):
    rel = os.path.relpath(F, root)[:-5]
    script = R2_SCRIPT.replace("@F@", rel)
    sp = os.path.join(root, "grader-r2-world.lsp"); open(sp, "w").write(script)
    try:
        r = subprocess.run([ACL2], cwd=root, stdin=open(sp), capture_output=True, text=True,
                           timeout=1800, env=env)
        out = r.stdout
    except subprocess.TimeoutExpired:
        out = ""
    open(log, "w").write(out)
    vals = {}
    for k in ("TRUSTED1", "TRUSTED2", "VERIFIED", "TTAGS", "TTAGS-NOT-VIA-F"):
        m = re.search(r"GRADER-" + k + r" (.*)", out)
        vals[k] = m.group(1).strip() if m else None
    vals["done"] = "GRADER-R2-DONE" in out
    return vals

def sexp_len(s):
    f = parse(tokens(s))
    return len(f[0]) if f and isinstance(f[0], list) else 0

# ---------------------------------------------------------------- main
def main():
    work = os.path.abspath(sys.argv[1])
    tmp = tempfile.mkdtemp(prefix="grade-tool-smtlink3-")
    root = os.path.join(tmp, "work")
    shutil.copytree(work, root, symlinks=False, ignore=shutil.ignore_patterns(
        "*.cert", "*.cert.out", "*.cert.time", "*.port", "*.fasl", "*.*fsl", "*.pcert0", "*.pcert1",
        "*.acl2x", "*.out", "grader", ".git"))
    print(f"grading copy: {root}")
    real_z3 = shutil.which("z3")
    bins = make_wrappers(tmp, real_z3)
    logs = os.path.join(tmp, "z3log")
    res = {}

    def env_for(mode, logname):
        e = dict(os.environ)
        e["PATH"] = bins[mode] + ":" + e.get("PATH", "")
        e["GRADER_Z3_LOG"] = os.path.join(logs, logname)
        return e

    # 2. scan
    banned, trusted_files, allowed = scan(root)
    for b in banned: print("BANNED " + b)
    F = trusted_files[0][0] if len(trusted_files) == 1 and trusted_files[0][1] == 1 else None
    if F: print(f"trusted clause processor book: {os.path.relpath(F, root)}; ttag-allowed books: "
                + ", ".join(sorted(os.path.relpath(p, root) for p in allowed)))
    else: print("trusted clause processor definitions: " +
                (", ".join(f"{os.path.relpath(p, root)} x{n}" for p, n in trusted_files) or "none"))

    # 3. certify model books
    ensure_ttag_flags(root)
    books = [os.path.relpath(p, root) for p in model_files(root) if p.endswith(".lisp")]
    rc = run_cert(root, books, env_for("real", "model"), os.path.join(tmp, "cert-model.log"), MODEL_TIMEOUT)
    failed = [b for b in books if not certified(os.path.join(root, b[:-5]))]
    print(f"model books: {len(books)}; not certified: {failed or 'none'} (log {tmp}/cert-model.log)")

    # 4. grader books
    gdir = os.path.join(root, "grader")
    shutil.copytree(os.path.join(HERE, "books"), gdir)
    gres = {}
    plan = [("grader-common", "real"), ("grade-r3", "real"), ("grade-r4", "real"), ("grade-r6", "real"),
            ("grade-r7", "real"), ("grade-r3-unknown", "unknown"), ("grade-r3-error", "error")]
    deps_ok = certified(os.path.join(root, "smtlink")) and certified(os.path.join(root, "examples"))
    for b, mode in plan:
        if not deps_ok:  # do not let cert.pl retry the model's books (possibly under a fake z3)
            gres[b] = False; print(f"grader book {b}: skipped (smtlink/examples not certified)"); continue
        run_cert(gdir, [b + ".lisp"], env_for(mode, b), os.path.join(tmp, f"cert-{b}.log"), BOOK_TIMEOUT)
        gres[b] = certified(os.path.join(gdir, b))
        print(f"grader book {b} ({mode} z3): {'certified' if gres[b] else 'FAILED'} (log {tmp}/cert-{b}.log)")
    calls = {b: z3_calls(os.path.join(logs, b)) for b, _ in plan}
    calls["model"] = z3_calls(os.path.join(logs, "model"))
    total_real = sum(len(calls[b]) for b in ("model", "grade-r3", "grade-r4", "grade-r6", "grade-r7"))
    via_path = total_real > 0
    if not via_path:
        print("NOTE: no z3 call went through the PATH wrapper; solver-log checks become MANUAL")
    unsat_in = lambda b: any(re.match(r"\s*unsat\b", c["output"]) for c in calls[b])
    common_ok = gres["grader-common"]
    common_msg = "" if common_ok else "grader-common (include of smtlink + examples) did not certify; "

    # structural
    st = structural(root)
    smt_ok = certified(os.path.join(root, "smtlink"))
    ex_ok = certified(os.path.join(root, "examples"))

    # R1
    srcs = {p: open(p, errors="replace").read() for p in model_files(root)}
    code_toks = [unpkg(t) for s in srcs.values() for t in tokens(s)]
    py = sorted({os.path.relpath(p, root) for p, s in srcs.items()
                 if any("python" in t.lower() for t in tokens(s))})
    scripts = [c for k in calls for c in calls[k] if k in ("model", "grade-r3", "grade-r4", "grade-r6", "grade-r7")]
    if not os.path.exists(os.path.join(root, "smtlink.lisp")): res[1] = ("FAIL", "smtlink.lisp missing")
    elif not smt_ok: res[1] = ("FAIL", "smtlink.lisp does not certify")
    elif "rewrite$" not in code_toks: res[1] = ("FAIL", "rewrite$ is not used anywhere in the model's books")
    elif via_path and not any(re.search(r"\(\s*check-sat\s*\)", c["input"]) for c in scripts):
        res[1] = ("FAIL", "z3 was called but never with an SMT-LIB script containing (check-sat)")
    else:
        res[1] = ("MANUAL", "inspect the clause-processor chain (CHECKLIST R1)" +
                  ("" if via_path else "; z3 not called via PATH: check SMT-LIB generation by hand") +
                  (f"; files mentioning python: {py}" if py else "; no file mentions python"))

    # R2
    if not F:
        res[2] = ("FAIL", "need exactly one define-trusted-clause-processor in the model's files, found "
                  + (", ".join(f"{os.path.relpath(p, root)} x{n}" for p, n in trusted_files) or "none"))
    elif any("outside the trusted" in b for b in banned):
        res[2] = ("FAIL", "trust-tag machinery outside the trusted clause processor's books (see BANNED lines)")
    elif not (smt_ok and ex_ok):
        res[2] = ("FAIL", "smtlink/examples not certified; world check impossible")
    else:
        v = r2_world(root, F, env_for("real", "r2"), os.path.join(tmp, "r2-world.log"))
        print(f"R2 world: trusted after F: {v['TRUSTED1']}; trusted after all: {v['TRUSTED2']}; "
              f"verified cl-procs: {v['VERIFIED']}; ttags-seen: {v['TTAGS']}; not via F: {v['TTAGS-NOT-VIA-F']}")
        if not v["done"] or v["TRUSTED2"] is None:
            res[2] = ("FAIL", f"world check did not complete (log {tmp}/r2-world.log)")
        elif sexp_len(v["TRUSTED2"]) != 1:
            res[2] = ("FAIL", f"trusted clause processors in the world: {v['TRUSTED2']} (want exactly one)")
        elif v["TRUSTED1"] != v["TRUSTED2"]:
            res[2] = ("FAIL", f"trusted clause processor not from {os.path.relpath(F, root)}: {v['TRUSTED2']}")
        elif v["TTAGS-NOT-VIA-F"] not in ("NIL", None):
            res[2] = ("FAIL", f"ttags not reached through the trusted book: {v['TTAGS-NOT-VIA-F']}")
        elif sexp_len(v["VERIFIED"] or "()") == 0:
            res[2] = ("FAIL", "no verified (:clause-processor rule) clause processor in the world")
        else:
            res[2] = ("MANUAL", f"one trusted CP {v['TRUSTED2']}; verified CP rules {v['VERIFIED']}: "
                      "inspect side goals per CHECKLIST R2")

    # R3
    fails, manual = [], []
    if not common_ok: fails.append(common_msg)
    elif not gres["grade-r3"]: fails.append("grade-r3 (true goal proves, false goal must-fail) did not certify")
    if common_ok:
        for b, what in (("grade-r3-unknown", "unknown"), ("grade-r3-error", "error")):
            if calls[b]:
                if not gres[b]: fails.append(f"goal proved although z3 answered {what}")
            elif gres[b]:
                manual.append(f"with the fake z3 ({what}) the proof failed but the fake was never called")
            else:
                manual.append(f"with the fake z3 ({what}) the goal still proved and the fake was never called")
        logic = [c for c in scripts if c["input"].strip()]
        if via_path and logic and not all(re.search(r"\(\s*set-logic\s+AUFNIRA\s*\)", c["input"]) for c in logic):
            fails.append("an SMT-LIB script without (set-logic AUFNIRA): " + next(
                c["dir"] for c in logic if not re.search(r"\(\s*set-logic\s+AUFNIRA\s*\)", c["input"])))
        if via_path and not logic: manual.append("no solver input captured (z3 given input some other way)")
        if not via_path: manual.append("z3 not called via PATH: check AUFNIRA and unknown/error handling by hand")
    if fails: res[3] = ("FAIL", "; ".join(fails))
    elif manual: res[3] = ("MANUAL", "; ".join(manual) + " (CHECKLIST R3)")
    else: res[3] = ("PASS", "")

    # R4
    if not ex_ok: res[4] = ("FAIL", "examples.lisp does not certify")
    elif not st[4][0]: res[4] = ("FAIL", st[4][1])
    elif not common_ok: res[4] = ("FAIL", common_msg)
    elif not gres["grade-r4"]: res[4] = ("FAIL", "the paper's goal / permuted goal with the paper's hint did not prove (grade-r4)")
    elif via_path and not unsat_in("grade-r4"): res[4] = ("FAIL", "grade-r4 proved without a z3 call answering unsat")
    else: res[4] = ("PASS", "") if via_path else ("MANUAL", "proofs pass; confirm Z3 is really called (CHECKLIST R4)")

    # R5
    if not ex_ok: res[5] = ("FAIL", "examples.lisp does not certify")
    elif st[5][0] is True: res[5] = ("PASS", "")
    elif st[5][0] == "manual": res[5] = ("MANUAL", st[5][1])
    else: res[5] = ("FAIL", st[5][1])

    # R6
    if not ex_ok: res[6] = ("FAIL", "examples.lisp does not certify")
    elif not st[6][0]: res[6] = ("FAIL", st[6][1])
    elif common_ok and gres["grade-r6"] and (not via_path or calls["grade-r6"]): res[6] = ("PASS", "")
    else: res[6] = ("MANUAL", st[6][1] + "; but the grader's own type-terse goal (grade-r6, rational theory) "
                    "did not prove with a z3 call: see CHECKLIST R6")

    # R7
    if not ex_ok: res[7] = ("FAIL", "examples.lisp does not certify")
    elif not st[7][0]: res[7] = ("FAIL", st[7][1])
    elif common_ok and gres["grade-r7"] and (not via_path or unsat_in("grade-r7")): res[7] = ("PASS", "")
    else: res[7] = ("MANUAL", st[7][1] + "; but the grader's restatement (grade-r7) did not prove with a z3 "
                    "unsat answer: see CHECKLIST R7")

    # R8
    rd = os.path.join(root, "README.md")
    res[8] = ("FAIL", "README.md missing") if not os.path.exists(rd) else \
             ("MANUAL", "follow README.md to print the SMT-LIB script and rewritten term of poly-ineq-example (CHECKLIST R8)")

    # R9
    if failed: res[9] = ("FAIL", "not certified: " + ", ".join(failed))
    elif banned: res[9] = ("FAIL", "banned events present (see BANNED lines)")
    elif not books: res[9] = ("FAIL", "no books")
    else: res[9] = ("PASS", "")

    for n in range(1, 10):
        s, why = res[n]
        print(f"R{n} {s}" + (f" {why}" if why else ""))
    nfail = sum(1 for n in res if res[n][0] == "FAIL")
    nman = sum(1 for n in res if res[n][0] == "MANUAL")
    print(f"SUMMARY tool-smtlink3: {9 - nfail - nman} PASS, {nfail} FAIL, {nman} MANUAL"
          + (f", {len(banned)} BANNED" if banned else "") + f"; files in {tmp}")
    sys.exit(0 if nfail == 0 and not banned else 1)

if __name__ == "__main__":
    main()
