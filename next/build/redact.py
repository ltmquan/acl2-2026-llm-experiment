#!/usr/bin/env python3
"""Paper text for the tool tasks: pdftotext -layout, with pointers to the authors' own implementation removed."""
import re, subprocess, os
SRC = "/home/user/acl2-exp/papers"; OUT = "/home/user/acl2-exp/next-build/papers"
R = "[removed]"
RULES = {
  "coglio-jurgensen-definductive": [r"\[books\]/std/util/definductive\.lisp"],
  "chen-smtlink3": [],
  "bora-erlang": [r"https://github\.com/KuterBora/Erlang-in-ACL2"],
  "gamboa-remora": [],
  "hardin-arrayset": [],
  "mccarthy-aes": [r"https://github\.com/bendyarm/aeneas-acl2-devenv,?", r"doi:10\.5281/zenodo\.22365956\.?",
                   r"DOI 10\.5281/zenodo\.22365956", r"ghcr\.io/bendyarm/aeneas-acl2-dev(:[\w.-]+)?",
                   r"bendyarm/aeneas", r"bendyarm/charon", r"\b[0-9a-f]{40}\b", r"\b(23cf8c8|58b7d54|0612757|b652707d|340b1af4)\w*",
                   r"sha256:[0-9a-f]{64}"],
}
for p, rules in RULES.items():
    t = subprocess.run(["pdftotext", "-layout", f"{SRC}/{p}.pdf", "-"], capture_output=True, text=True, check=True).stdout
    n = 0
    for r in rules:
        t, k = re.subn(r, R, t); n += k
    t = t.replace("\f", "\n")
    t = re.sub(r"[ \t]+\n", "\n", t)
    open(f"{OUT}/{p}.txt", "w").write(t)
    print(p, len(t), "bytes,", n, "redactions")
