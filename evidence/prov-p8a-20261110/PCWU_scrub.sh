#!/bin/bash
# Drop every emitted .lean file that contains a sorry placeholder (never committed); keep its sha256 in <dir>/raw.sha256.
set -euo pipefail
cd "$(dirname "$0")"
for d in PCWU_E*_emitted/raw; do
  [ -d "$d" ] || continue
  for f in $(grep -rl -w sorry "$d" --include='*.lean' || true); do
    h=$(shasum -a 256 "$f" | cut -d' ' -f1)
    echo "$h  ${f#*/raw/}  DROPPED_CONTAINS_SORRY" >> "${d%/raw}/raw.sha256"
    rm "$f"
  done
done
grep -rlw sorry . --include='*.lean' && { echo "sorry remains"; exit 1; } || echo "no sorry in .lean files"
