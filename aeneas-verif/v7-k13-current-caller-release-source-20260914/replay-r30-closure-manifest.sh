#!/usr/bin/env bash
set -euo pipefail
bundle=${1:?bundle required}
stage=${2:?validated deterministic R29 stage required}
output=${3:?fresh replay output required}
revision=${4:?source revision required}
root=/home/dombarker/project-offloads/v7-gate-closure-prechallenge-return-r22
backend=$root/aeneas-lean-formatter-unit-r26
aspis=/home/dombarker/project-offloads/aspis-v7-root-sweep-20260909/AspisFormal
if [[ -e "$output" ]]; then
  echo 'refusing to overwrite replay output' >&2
  exit 2
fi
python3 "$bundle/toolchain/r30-closure-manifest.py" "$bundle" "$stage"
formatter=$backend/Aeneas/Std/Core/Fmt.lean
formatter_expected=e7e6e37c6271592f934dfcbde894a7b8e1afd19c2c8db41bd683e650beb889c8
[[ $(sha256sum "$formatter" | cut -d ' ' -f 1) == "$formatter_expected" ]]
mkdir -p "$output"
export LEAN_PATH="$output:$root/arithmetic-lean432-cache-current:$aspis/.lake-root-sweep/lib/lean:$backend/.lake/build/lib/lean"
for directory in "$aspis"/.lake/packages/*/.lake/build/lib/lean "$backend"/.lake/packages/*/.lake/build/lib/lean; do
  LEAN_PATH="$LEAN_PATH:$directory"
done
export LEAN_NUM_THREADS=1
cd "$backend"
printf 'SOURCE_REVISION=%s\n' "$revision"
/home/dombarker/.elan/bin/lake env lean --version
sha256sum "$bundle/R30-CLOSURE-MANIFEST.sha256" "$bundle/R30-CLOSURE-ORDER.tsv"
count=0
while IFS=$'\t' read -r module relative; do
  case "$relative" in
    staged-r29/*) source=$stage/${relative#staged-r29/} ;;
    *) source=$bundle/$relative ;;
  esac
  destination=$output/${module//./\/}.olean
  mkdir -p "$(dirname "$destination")"
  printf 'START target=%s source=%s\n' "$module" "$relative"
  /usr/bin/time -f "RESULT target=$module exit=%x wall_s=%e peak_kib=%M swaps=%W" \
    /home/dombarker/.elan/bin/lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -o "$destination" "$source"
  count=$((count + 1))
done < "$bundle/R30-CLOSURE-ORDER.tsv"
printf 'FINAL target=V7ProductionSnapshotObserverR30ClosureAxioms modules=%s status=passed\n' "$count"
