#!/bin/bash
# Grader for tool-smtlink3.  Usage: grade.sh <work-dir>
# Copies <work-dir> to a fresh temp dir and does all checks there; see grade.py and CHECKLIST.md.
set -u
[ $# -eq 1 ] || { echo "usage: $0 <work-dir>" >&2; exit 2; }
exec python3 -I "$(cd "$(dirname "$0")" && pwd)/grade.py" "$1"
