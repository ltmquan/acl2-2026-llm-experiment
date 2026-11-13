#!/bin/bash
# usage: try.sh dir  -> certifies defs.lisp in dir, prints OK/FAIL
cd $1; rm -f defs.cert defs.cert.out; perl /opt/acl2/books/build/cert.pl --acl2 /opt/acl2/saved_acl2 defs.lisp > cert.log 2>&1; if [ -f defs.cert ]; then echo OK; else echo FAIL; grep -n "ACL2 Error" defs.cert.out | head -3; fi
