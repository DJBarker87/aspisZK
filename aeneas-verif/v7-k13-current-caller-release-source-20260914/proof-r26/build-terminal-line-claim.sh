#!/usr/bin/env sh
set -eu

proof=/home/dombarker/project-offloads/v7-gate-closure-prechallenge-return-r22/r26-proof-432
cache=/home/dombarker/project-offloads/v7-gate-closure-prechallenge-return-r22/r26-proof-432-cache
arith=/home/dombarker/project-offloads/v7-gate-closure-prechallenge-return-r22/arithmetic-lean432-cache-current
generated=/home/dombarker/project-offloads/v7-gate-closure-prechallenge-return-r22/generated-r26
backend=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
aspis=/home/dombarker/project-offloads/aspis-v7-root-sweep-20260909/AspisFormal
packages=""
for d in "$aspis"/.lake/packages/*/.lake/build/lib/lean "$backend"/.lake/packages/*/.lake/build/lib/lean; do
  packages="${packages:+$packages:}$d"
done
export LEAN_PATH="$cache:$proof:$arith:$generated:$aspis/.lake-root-sweep/lib/lean:$backend/.lake/build/lib/lean:$packages"
exec /usr/bin/time -v /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -o "$proof/V7CallerCurrentReleaseR26TerminalLineClaim.olean" \
  "$proof/V7CallerCurrentReleaseR26TerminalLineClaim.lean"
