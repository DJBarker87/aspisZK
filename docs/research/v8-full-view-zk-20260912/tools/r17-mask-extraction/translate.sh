#!/usr/bin/env bash
set -euo pipefail
# Run in a bounded, zero-swap scope. Generated external templates are evidence,
# never accepted proofs and never renamed into compilable axiom dependencies.
input=${1:?LLBC artifact required}
expected=${2:?recorded LLBC sha256 required}
output=${3:?fresh output directory required}
aeneas=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1
test "$(sha256sum "$aeneas" | cut -d' ' -f1)" = e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813
test "$(sha256sum "$input" | cut -d' ' -f1)" = "$expected"
test ! -e "$output"
exec /usr/bin/time -v "$aeneas" -sequential -no-progress-bar -abort-on-error \
  -backend lean -namespace AspisR17MaskSource -dest "$output" \
  -subdir AspisR17MaskSource -split-files -emit-json "$input"
