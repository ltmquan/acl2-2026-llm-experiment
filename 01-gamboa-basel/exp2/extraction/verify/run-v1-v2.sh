#!/bin/sh
# V1 + V2: certify defs.lisp and the skip-proofs target test book in a scratch copy, ACL2(r) 8.7.
set -e
G=/home/user/acl2-exp/exp2/given/gamboa-basel
S=${1:-<scratch>/given-gamboa-basel}
rm -rf "$S"; mkdir -p "$S"
cp $G/defs.lisp $G/verify/test-targets.lisp $G/verify/test-targets.acl2 "$S"/
cd "$S" && perl /opt/acl2/books/build/cert.pl --acl2 /opt/acl2r/saved_acl2r defs.lisp test-targets.lisp
