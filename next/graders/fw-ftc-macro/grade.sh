#!/bin/sh
# Grader for fw-ftc-macro.  Usage: grade.sh <work-dir>   (see grade.py, CHECKLIST.md, NOTES.md)
exec python3 -I "$(dirname "$0")/grade.py" "$@"
