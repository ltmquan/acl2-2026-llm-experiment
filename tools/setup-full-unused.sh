#!/bin/bash
# Setup for model-run sessions: ACL2 8.7 + ACL2(r) 8.7 with books, no git history.
set -euo pipefail
ROOT="${ACL2_ROOT:-/opt}"
command -v sbcl >/dev/null || { apt-get update -qq && apt-get install -y -qq sbcl; }
if [ ! -x "$ROOT/acl2/saved_acl2" ]; then
  git clone -q --depth 1 --branch 8.7 https://github.com/acl2/acl2.git "$ROOT/acl2"
  rm -rf "$ROOT/acl2/.git"
  cp -a "$ROOT/acl2" "$ROOT/acl2r"
  (cd "$ROOT/acl2" && make -s LISP=sbcl >/dev/null) & P1=$!
  (cd "$ROOT/acl2r" && make -s LISP=sbcl ACL2_REAL=r >/dev/null) & P2=$!
  wait $P1; wait $P2
  (cd "$ROOT/acl2/books" && make -s -j2 basic ACL2="$ROOT/acl2/saved_acl2" >/dev/null) & P1=$!
  (cd "$ROOT/acl2r/books" && make -s -j2 basic ACL2="$ROOT/acl2r/saved_acl2r" >/dev/null) & P2=$!
  wait $P1; wait $P2
  (cd "$ROOT/acl2/books" && build/cert.pl -q -j4 --acl2 "$ROOT/acl2/saved_acl2" projects/linear/*.lisp)
  (cd "$ROOT/acl2r/books" && build/cert.pl -q -j4 --acl2 "$ROOT/acl2r/saved_acl2r" \
     nonstd/nsa/*.lisp nonstd/integrals/*.lisp nonstd/circles/*.lisp arithmetic/factorial.lisp \
     $(find nonstd/workshops/2011/reid-gamboa-differentiator -name '*.lisp'))
fi
BIN="${ACL2_BIN:-/usr/local/bin}"
mkdir -p "$BIN"
ln -sf "$ROOT/acl2/saved_acl2" "$BIN/acl2"
ln -sf "$ROOT/acl2r/saved_acl2r" "$BIN/acl2r"
ln -sf "$ROOT/acl2/books/build/cert.pl" "$BIN/cert.pl"
mkdir -p "${WORK_DIR:-/work}"
