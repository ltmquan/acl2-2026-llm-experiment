#!/bin/sh
# wrapgen.sh SRC FN LEMMA... : local encapsulate with FN enabled holding the authors' /// lemmas
src=$1; fn=$2; shift 2
echo ";; Local copies of lemmas from the /// section of $fn ($(basename $src)),"
echo ";; proved, as there, with $fn enabled."
echo "(local"
echo " (encapsulate ()"
echo "  (local (in-theory (enable $fn)))"
echo
python3 -I $(dirname $0)/extract.py -raw $src "$@"
echo "))"
