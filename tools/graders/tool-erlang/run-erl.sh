#!/bin/bash
# Helper for the manual checks R1/R4 of tool-erlang (see CHECKLIST.md).
# Usage: run-erl.sh <graded-copy-work-dir> <file.erl> '<convert command>' '<acl2 forms>'
#   <graded-copy-work-dir>  the "grading copy" directory printed by grade.sh (books already certified)
#   <file.erl>              e.g. erlang/add_pairs.erl from this grader directory
#   <convert command>       the README's exact command, with {erl} for the .erl file and {out} for the
#                           output file if the command writes one (if it prints to stdout, leave {out}
#                           out: stdout is saved to {out} = grader-erl/<module>.lisp)
#   <acl2 forms>            the README's load form(s) and run form, with {out} for the converted file,
#                           e.g. '(include-book "examples") (ld "{out}") (run ... )'
# Runs the conversion in <copy>/ , then the ACL2 forms in a fresh ACL2 8.7 started in <copy>/, and
# prints the conversion output and the tail of the ACL2 transcript for the person to compare.
set -u
[ $# -eq 4 ] || { sed -n '2,13p' "$0"; exit 2; }
copy=$(cd "$1" && pwd); erl=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
mod=$(basename "$2" .erl); mkdir -p "$copy/grader-erl"; cp "$erl" "$copy/grader-erl/"
in="$copy/grader-erl/$mod.erl"; out="$copy/grader-erl/$mod.lisp"
conv=${3//\{erl\}/$in}; conv2=${conv//\{out\}/$out}
echo "== converting: $conv2"
if [[ "$conv" == *"{out}"* ]]; then (cd "$copy" && bash -c "$conv2"); rc=$?
else (cd "$copy" && bash -c "$conv2" > "$out"); rc=$?; fi
echo "== conversion exit status $rc; output file $out:"; head -c 3000 "$out" 2>/dev/null; echo
forms=${4//\{out\}/$out}
echo "== ACL2: $forms"
(cd "$copy" && printf '%s\n' "$forms" | /opt/acl2/saved_acl2 2>&1 | tail -n 80)
