#!/usr/bin/env python3
"""Build the experiment-2 prompt for one paper from exp2/given/<paper>/{defs.lisp,targets.lisp,README.md}.
Usage: python3 -I make-prompt.py <paper-id>  -> writes exp2/prompts/<paper-id>.txt and prints its size."""
import sys, os, re
root = "/home/user/acl2-exp/exp2"
p = sys.argv[1]; g = os.path.join(root, "given", p)
pd = os.path.join(g, "prompt")
src = pd if os.path.exists(os.path.join(pd, "defs.lisp")) else g
def nocomments(t):
    lines = [l for l in t.splitlines()
             if not l.lstrip().startswith(";") or l.lstrip().lower().startswith("; cert-flags:")]
    out = []
    for l in lines:
        if l.strip() == "" and out and out[-1].strip() == "":
            continue
        out.append(l.rstrip())
    return "\n".join(out).strip() + "\n"
defs = nocomments(open(os.path.join(src, "defs.lisp")).read())
extra = []   # (filename, content)
for fn in ("cert.acl2", "defs.acl2"):
    fp = os.path.join(src, fn)
    if os.path.exists(fp):
        extra.append((fn, nocomments(open(fp).read()) if fn != "defs.acl2" else open(fp).read().rstrip() + "\n"))
targets = open(os.path.join(g, "targets.lisp")).read()
# targets shown to the model without the provenance comments (they name the authors' theorems)
shown = "\n".join(l for l in targets.splitlines() if not l.lstrip().startswith(";")).strip() + "\n"
names = re.findall(r"\(defthm\s+(\S+)", shown, re.I)
files = "".join(f"\n<{fn}>\n{c}</{fn}>\n" for fn, c in extra)
names_files = ", ".join(["/work/defs.lisp"] + [f"/work/{fn}" for fn, _ in extra])
skipnote = ("" if "skip-proofs" not in defs else
            " Some definitions in defs.lisp are admitted with skip-proofs: their admissibility has been checked "
            "separately, and cert.acl2 permits skip-proofs so that books including defs.lisp can be certified. "
            "Your own files must not use skip-proofs: your solution will be checked against fully proved "
            "definitions without that permission.")
prompt = f"""Prove the theorems below in ACL2.

1. Create {names_files}{", each" if extra else ""} containing exactly the text between {"its" if extra else "the"} tags. defs.lisp holds the definitions the theorems use. Do not modify these files.{skipnote}

<defs.lisp>
{defs}</defs.lisp>
{files}
2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given ({", ".join(n.upper() for n in names)}). You may add your own definitions and lemmas before them.

<theorems>
{shown}</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
"""
out = os.path.join(root, "prompts", p + ".txt")
open(out, "w").write(prompt)
print(f"{p}: {len(prompt.encode())} bytes, {prompt.count(chr(10))} lines, targets={names}")
