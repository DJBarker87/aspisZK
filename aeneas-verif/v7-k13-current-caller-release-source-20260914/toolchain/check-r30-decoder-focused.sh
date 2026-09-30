#!/usr/bin/env bash
set -euo pipefail
revision=${1:?source revision required}
root=/home/dombarker/project-offloads/v7-gate-closure-prechallenge-return-r22
backend=$root/aeneas-lean-formatter-unit-r26
aspis=/home/dombarker/project-offloads/aspis-v7-root-sweep-20260909/AspisFormal
cache=/home/dombarker/project-offloads/v7-e2e-r27-output
export LEAN_PATH="$cache/r30:$cache/lean:$cache/callback-r29:$root/r26-final-replay-34bb5ecd:$root/arithmetic-lean432-cache-current:$aspis/.lake-root-sweep/lib/lean:$backend/.lake/build/lib/lean"
for directory in "$aspis"/.lake/packages/*/.lake/build/lib/lean "$backend"/.lake/packages/*/.lake/build/lib/lean; do
  LEAN_PATH="$LEAN_PATH:$directory"
done
export LEAN_NUM_THREADS=1
cd "$backend"
printf 'SOURCE_REVISION=%s\n' "$revision"
sha256sum "$cache/r30/V7ProductionCallbacksR30DecoderCanonical.lean"
/usr/bin/time -f 'RESULT target=V7ProductionCallbacksR30DecoderCanonical exit=%x wall_s=%e peak_kib=%M swaps=%W' \
  /home/dombarker/.elan/bin/lake env lean -j1 -R "$cache/r30" \
  -o "$cache/r30/V7ProductionCallbacksR30DecoderCanonical.olean" \
  "$cache/r30/V7ProductionCallbacksR30DecoderCanonical.lean"
