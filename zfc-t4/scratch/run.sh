#!/bin/bash
# usage: run.sh file.lisp  -- loads defs then file events
cd /work
cat > /tmp/run-$$.lsp <<EOT
(include-book "projects/set-theory/portcullis" :dir :system)
(in-package "ZF")
(include-book "defs")
(set-inhibit-output-lst '(proof-tree))
(ld "$1" :ld-error-action :error)
(good-bye)
EOT
acl2 < /tmp/run-$$.lsp 2>&1
rm -f /tmp/run-$$.lsp
