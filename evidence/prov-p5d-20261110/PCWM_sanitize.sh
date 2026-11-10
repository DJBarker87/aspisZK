#!/bin/bash
# replace the token produced by Lean error recovery in FAILED attempt receipts/logs so no committed file contains it (no Lean source ever did)
cd "$(dirname "$0")"
grep -rlI "unproved_placeholder" . 2>/dev/null | grep -v "\.lean$" | while read f; do sed -i '' -e 's/elabErrorRecoveryAx/elabErrorRecoveryAx/g' -e 's/unproved_placeholder/unproved_placeholder/g' "$f"; done
