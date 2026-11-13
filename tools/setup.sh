#!/bin/bash
# Setup for model-run sessions (slim): ACL2 8.7 + ACL2(r) 8.7, no git history, core + task books certified.
set -euo pipefail
ROOT="${ACL2_ROOT:-/opt}"
J=$(nproc)
ts() { echo "[setup $(date -u +%H:%M:%S)] $*"; }
BIN="${ACL2_BIN:-/usr/local/bin}"
mkdir -p "$BIN" "${WORK_DIR:-/work}"
ln -sf "$ROOT/acl2/saved_acl2" "$BIN/acl2"
ln -sf "$ROOT/acl2r/saved_acl2r" "$BIN/acl2r"
ln -sf "$ROOT/acl2/books/build/cert.pl" "$BIN/cert.pl"
command -v sbcl >/dev/null || { apt-get update -qq && apt-get install -y -qq sbcl >/dev/null; }
if [ ! -x "$ROOT/acl2/saved_acl2" ]; then
  ts "clone 8.7"; git clone -q --depth 1 --branch 8.7 https://github.com/acl2/acl2.git "$ROOT/acl2" 2>/dev/null
  rm -rf "$ROOT/acl2/.git"; cp -a "$ROOT/acl2" "$ROOT/acl2r"
  ts "redirect GitHub for git"
  git config --system url."https://github.invalid/".insteadOf "https://github.com/"
  git config --system --add url."https://github.invalid/".insteadOf "git@github.com:"
  ts "build images"
  (cd "$ROOT/acl2" && make -s LISP=sbcl >/dev/null) & P1=$!
  (cd "$ROOT/acl2r" && make -s LISP=sbcl ACL2_REAL=r >/dev/null) & P2=$!
  wait $P1; wait $P2
  ts "certify ACL2(r) books"
  (cd "$ROOT/acl2r/books" && build/cert.pl -q -j "$J" --acl2 "$ROOT/acl2r/saved_acl2r" arithmetic-5/top.lisp \
     nonstd/nsa/*.lisp nonstd/integrals/*.lisp nonstd/circles/*.lisp arithmetic/factorial.lisp \
     $(find nonstd/workshops/2011/reid-gamboa-differentiator -name '*.lisp'))
  ts "certify ACL2 books"
  (cd "$ROOT/acl2/books" && build/cert.pl -q -j "$J" --acl2 "$ROOT/acl2/saved_acl2" std/top.lisp \
     arithmetic/top-with-meta.lisp arithmetic-5/top.lisp ihs/ihs-lemmas.lisp misc/records.lisp)
fi
ts "network probe (what the model can reach)"
for u in https://github.com https://raw.githubusercontent.com/acl2/acl2/master/README.md https://arxiv.org https://example.com https://www.cs.utexas.edu/~moore/acl2/; do
  echo "  $u -> $(curl -s -o /dev/null -w '%{http_code}' --max-time 10 "$u" || true)"
done
echo "  git ls-remote github -> $(timeout 20 git ls-remote https://github.com/acl2/acl2.git HEAD >/dev/null 2>&1 && echo reachable || echo blocked)"
ts "done"
