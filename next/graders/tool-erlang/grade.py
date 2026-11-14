#!/usr/bin/env python3
"""Grader for tool-erlang (ACL2 8.7, paper bora-erlang).

Usage: python3 -I grade.py <work-dir>      (grade.sh is a thin wrapper)

Prints one line per requirement of next/tasks/tool-erlang/prompt.txt:
  R<n> PASS | R<n> FAIL <reason> | R<n> MANUAL <what to inspect (see CHECKLIST.md)>
then a SUMMARY line.  Exit 0 iff no requirement FAILs and no banned event was found.

The paper fixes few names, so most requirements are MANUAL after mechanical preconditions:
 1. copy <work-dir> to a fresh temp dir (no stale .cert/.port/compiled files);
 2. scan the model's .lisp/.lsp/.acl2 files for banned events (skip-proofs, defaxiom, trust tags,
    redefinition, ...), and cert-flags that allow skip-proofs/defaxioms/ttags;
 3. certify every model .lisp file with cert.pl and default cert flags;
 4. copy books/ to <copy>/grader/ and certify: grade-r2 (eval-cont-list exists, logic mode,
    recursive), grade-r3 (a constrained function of the model's books has an attachment),
    grade-r5 (sum-of-nats, sum-test-world-p, erl-val-integer->val, make-erl-val-integer exist;
    sum-of-nats computes N(N+1)/2), grade-r6 (wtree-p, create-wtree exist);
 5. structural checks: assert-event forms in examples.lisp, defthms in sum-of-nats.lisp/reduce.lisp.
"""
import os, re, shutil, subprocess, sys, tempfile

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
BANNED = {"skip-proofs", "defaxiom", "set-ld-redefinition-action", "redef", "redef!", "redef+", "redef-",
          "set-skip-proofs", "skip-proofs-okp", "defun-unsound", "reset-prehistory", "defattach-system",
          "with-redef", "set-skip-proofs-okp", "defttag", "define-trusted-clause-processor", "progn!",
          "set-raw-mode", "set-raw-mode-on", "set-raw-mode-on!", "include-raw", "trust-tag",
          "remove-untouchable", "push-untouchable", "defmacro-last", "return-last-table",
          "set-temp-touchable-fns", "set-temp-touchable-vars", "defun-overrides", "open-trace-file!",
          "with-raw-mode", ":ttags", ":skip-checks"}

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

def scan(root):
    banned = []
    for p in model_files(root):
        rel = os.path.relpath(p, root)
        src = open(p, errors="replace").read()
        for f in parse(tokens(src)):
            for t in atoms_outside_defpkg(f):
                u = unpkg(t)
                if u in BANNED or u.startswith("sys-call"):
                    banned.append(f"{rel}: {u}")
        if p.endswith(".acl2"):
            for line in src.splitlines():
                m = re.match(r"^[ \t]*;[; \t]*cert-flags:(.*)$", line)
                if m and re.search(r":(skip-proofs-okp|defaxioms-okp|ttags)\s+(?!nil\b)", m.group(1), re.I):
                    banned.append(f"{rel}: cert-flags allow skip-proofs/defaxioms/ttags")
    return banned

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

# ---------------------------------------------------------------- structural
def heads(path, names):
    """Forms anywhere in the file whose head is in names, not under must-fail."""
    out = []
    def fn(f, ctx):
        if f and isinstance(f[0], str) and unpkg(f[0]) in names and \
           not any(c and unpkg(c).startswith("must-fail") for c in ctx):
            out.append(f)
    if os.path.exists(path):
        for f in parse(tokens(open(path, errors="replace").read())): walk(f, fn)
    return out

# ---------------------------------------------------------------- main
def main():
    work = os.path.abspath(sys.argv[1])
    tmp = tempfile.mkdtemp(prefix="grade-tool-erlang-")
    root = os.path.join(tmp, "work")
    shutil.copytree(work, root, symlinks=False, ignore=shutil.ignore_patterns(
        "*.cert", "*.cert.out", "*.cert.time", "*.port", "*.fasl", "*.*fsl", "*.pcert0", "*.pcert1",
        "*.acl2x", "*.beam", "grader", ".git"))
    print(f"grading copy: {root}")
    res = {}
    banned = scan(root)
    for b in banned: print("BANNED " + b)

    books = [os.path.relpath(p, root) for p in model_files(root) if p.endswith(".lisp")]
    run_cert(root, books, dict(os.environ), os.path.join(tmp, "cert-model.log"), MODEL_TIMEOUT)
    failed = [b for b in books if not certified(os.path.join(root, b[:-5]))]
    print(f"model books: {len(books)}; not certified: {failed or 'none'} (log {tmp}/cert-model.log)")
    ok = {b: certified(os.path.join(root, b)) for b in ("examples", "sum-of-nats", "reduce")}

    gdir = os.path.join(root, "grader")
    shutil.copytree(os.path.join(HERE, "books"), gdir)
    deps = {"grade-r2": ["examples"], "grade-r3": ["examples", "reduce"], "grade-r5": ["sum-of-nats"],
            "grade-r6": ["reduce"]}
    g = {}
    for b, ds in deps.items():
        if not all(ok[d] for d in ds):
            g[b] = False; print(f"grader book {b}: skipped ({', '.join(d for d in ds if not ok[d])} not certified)"); continue
        run_cert(gdir, [b + ".lisp"], dict(os.environ), os.path.join(tmp, f"cert-{b}.log"), BOOK_TIMEOUT)
        g[b] = certified(os.path.join(gdir, b))
        print(f"grader book {b}: {'certified' if g[b] else 'FAILED'} (log {tmp}/cert-{b}.log)")
        if b == "grade-r3" and g[b]:
            m = re.search(r"GRADER-R3-ATTACHMENTS (.*)", open(os.path.join(gdir, f"{b}.cert.out"), errors="replace").read())
            att = m.group(1) if m else "?"
            print(f"attachments added by the model's books: {att}")
    def need(book, why):
        return None if ok[book] else ("FAIL", f"{book}.lisp missing or does not certify" + why)

    # R1
    res[1] = ("FAIL", "README.md missing") if not os.path.exists(os.path.join(root, "README.md")) else \
             ("MANUAL", "run the front end per README.md on grader erlang/*.erl and on \"2 + 2.\" (CHECKLIST R1)")
    # R2
    res[2] = need("examples", "") or (("MANUAL", "eval-cont-list is a recursive logic-mode function; check fuel, "
              "out-of-fuel status and receive yield (CHECKLIST R2)") if g["grade-r2"] else
              ("FAIL", "no unique logic-mode recursive function eval-cont-list (grade-r2)"))
    # R3
    res[3] = need("examples", "") or need("reduce", "") or (("MANUAL", "attachment(s) to constrained functions exist; "
              "check the encapsulate's exported constraint is the fairness condition (CHECKLIST R3)") if g["grade-r3"]
              else ("FAIL", "no constrained function of the model's books has an attachment (grade-r3)"))
    # R4
    ae = heads(os.path.join(root, "examples.lisp"), ("assert-event", "assert!", "assert-equal", "assert?"))
    res[4] = need("examples", "") or (("MANUAL", f"{len(ae)} assert forms in examples.lisp; check they cover "
              "add_pairs, the two-process exchange and reduce (CHECKLIST R4)") if len(ae) >= 3 else
              ("FAIL", f"examples.lisp has {len(ae)} assert-event forms, need at least 3"))
    # R5
    th5 = heads(os.path.join(root, "sum-of-nats.lisp"), ("defthm", "defthmd"))
    res[5] = need("sum-of-nats", "") or (("FAIL", "paper's names missing or sum-of-nats wrong (grade-r5)")
              if not g["grade-r5"] else ("FAIL", "no defthm in sum-of-nats.lisp") if not th5 else
              ("MANUAL", "inspect the main theorem of sum-of-nats.lisp (CHECKLIST R5)"))
    # R6
    th6 = heads(os.path.join(root, "reduce.lisp"), ("defthm", "defthmd"))
    res[6] = need("reduce", "") or (("FAIL", "wtree-p / create-wtree missing (grade-r6)") if not g["grade-r6"] else
              ("FAIL", f"reduce.lisp has {len(th6)} defthms, need at least 3") if len(th6) < 3 else
              ("MANUAL", "identify and inspect the three reduce theorems (CHECKLIST R6)"))
    # R7
    if failed: res[7] = ("FAIL", "not certified: " + ", ".join(failed))
    elif banned: res[7] = ("FAIL", "banned events present (see BANNED lines)")
    elif not books: res[7] = ("FAIL", "no books")
    else: res[7] = ("PASS", "")

    for n in range(1, 8):
        s, why = res[n]
        print(f"R{n} {s}" + (f" {why}" if why else ""))
    nfail = sum(1 for n in res if res[n][0] == "FAIL")
    nman = sum(1 for n in res if res[n][0] == "MANUAL")
    print(f"SUMMARY tool-erlang: {7 - nfail - nman} PASS, {nfail} FAIL, {nman} MANUAL"
          + (f", {len(banned)} BANNED" if banned else "") + f"; files in {tmp}")
    sys.exit(0 if nfail == 0 and not banned else 1)

if __name__ == "__main__":
    main()
