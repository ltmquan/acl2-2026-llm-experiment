#!/bin/sh
# Grader for tool-aes-mir.  Usage: grade.sh <work-dir> [--adapter <file>]   (see grade.py, CHECKLIST.md, NOTES.md)
exec python3 -I "$(dirname "$0")/grade.py" "$@"
