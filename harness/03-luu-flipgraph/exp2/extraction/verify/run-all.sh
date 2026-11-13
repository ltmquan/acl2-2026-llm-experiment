#!/bin/sh
# Re-run V1-V3.  S = scratch dir holding a copy of the authors' books in $S/authors
# (certified there with: cert.pl --acl2 /opt/acl2/saved_acl2 -j 4 main.lisp scheme-algo.lisp).
set -e
S=${S:-<scratch>/given-luu-flipgraph}
V=$(cd "$(dirname "$0")" && pwd)
mkdir -p $S/v && cd $S/v
cp $V/../defs.lisp $V/v2-skip.lisp $V/v2-skip.acl2 $V/v3-authors.lisp $V/dump-*.lsp .
CERT="/opt/acl2/books/build/cert.pl --acl2 /opt/acl2/saved_acl2"
$CERT defs.lisp            # V1
$CERT v2-skip.lisp         # V2
$CERT v3-authors.lisp      # V3 (proofs from the authors' theorems)
for w in defs authors; do /opt/acl2/saved_acl2 < dump-$w.lsp > dump-$w.out 2>&1; done
cmp dump-defs.txt dump-authors.txt && echo "V3 definitions IDENTICAL"
python3 -I $V/textcheck.py $V/../defs.lisp /home/user/acl2-exp/reference-books/pr-2103/books/workshops/2026/luu-medley-manolios
