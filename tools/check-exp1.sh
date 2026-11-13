#!/bin/bash
# Mechanical check of a model's solution.lisp.
# Usage: check-solution.sh <solution.lisp> [acl2-image] [acl2r-image]
# Copies the file into a fresh temp dir, scans for banned events, certifies with ACL2 and,
# if that fails, with ACL2(r). Prints a one-line verdict and writes details to <dir>/check.log.
set -uo pipefail
SOL="$1"
ACL2="${2:-/opt/acl2/saved_acl2}"
ACL2R="${3:-/opt/acl2r/saved_acl2r}"
CERT=/opt/acl2/books/build/cert.pl
D=$(mktemp -d)
cp "$SOL" "$D/solution.lisp"
cd "$D"
LOG="$D/check.log"

# 1. Banned events / settings (case-insensitive, ignoring ;-comments).
BANNED='skip-proofs|defaxiom|defttag|set-ld-redefinition-action|skip-proofs-okp|:ttags|set-skip-proofs|trust-tag|define-trusted-clause-processor|defun-unsound|set-cbd|sys-call|reset-prehistory|redef'
HITS=$(sed 's/;.*$//' solution.lisp | grep -inE "$BANNED" || true)
if [ -n "$HITS" ]; then
  echo "BANNED: $(echo "$HITS" | head -3 | tr '\n' ' ')" | tee "$LOG"; echo "$D"; exit 2
fi

# 2. Last event must be (defthm MAIN ...) / (defthmd MAIN ...) / (defthm-std MAIN ...).
LAST=$(sed 's/;.*$//' solution.lisp | grep -inE '^\s*\((defthm|defthmd|defthm-std|defthmd-std|def|encapsulate|local|include-book|in-package|mutual-recursion|make-event|progn|with-|verify)' | tail -1)
if ! echo "$LAST" | grep -qiE '\((defthm|defthmd|defthm-std|defthmd-std)\s+main\b'; then
  echo "NO-MAIN: last top-level event is not a defthm named MAIN: $LAST" | tee "$LOG"; echo "$D"; exit 3
fi

# 3. Certify: plain ACL2 first, then ACL2(r).
for IMG in "$ACL2" "$ACL2R"; do
  rm -f solution.cert solution.cert.out
  if timeout 7200 perl "$CERT" --acl2 "$IMG" solution.lisp >>"$LOG" 2>&1 && [ -f solution.cert ]; then
    echo "CERTIFIED with $(basename "$IMG")"; echo "$D"; exit 0
  fi
done
echo "FAILED: did not certify with either image. Last 40 lines:"; tail -40 solution.cert.out 2>/dev/null || tail -40 "$LOG"
echo "$D"; exit 1
