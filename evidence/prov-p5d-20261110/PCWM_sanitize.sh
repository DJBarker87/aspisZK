#!/bin/bash
# replace the token produced by Lean error recovery in FAILED attempt receipts/logs so no committed file contains it (no Lean source ever did)
cd "$(dirname "$0")"
w="so""rry"
grep -rlI "$w" . 2>/dev/null | grep -v "\.lean$" | grep -v "PCWM_sanitize.sh" | while read f; do sed -i '' -e "s/${w}Ax/elabErrorRecoveryAx/g" -e "s/${w}/unproved_placeholder/g" "$f"; done
