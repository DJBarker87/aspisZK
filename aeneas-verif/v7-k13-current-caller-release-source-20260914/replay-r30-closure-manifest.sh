#!/usr/bin/env bash
set -euo pipefail
bundle=${1:?bundle required}
stage=${2:?validated deterministic R29 stage required}
output=${3:?fresh replay output required}
revision=${4:?source revision required}
mode=${5:-full}
[[ "$mode" == full || "$mode" == preflight ]]
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
scope_path=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
scope_directory=/sys/fs/cgroup$scope_path
[[ $(cat "$scope_directory/memory.high") == 7516192768 ]]
[[ $(cat "$scope_directory/memory.max") == 8589934592 ]]
[[ $(cat "$scope_directory/memory.swap.max") == 0 ]]
record_resources() {
  printf 'CGROUP peak_bytes=%s swap_current_bytes=%s high=%s max=%s swap_max=%s\n' \
    "$(cat "$scope_directory/memory.peak")" "$(cat "$scope_directory/memory.swap.current")" \
    "$(cat "$scope_directory/memory.high")" "$(cat "$scope_directory/memory.max")" \
    "$(cat "$scope_directory/memory.swap.max")"
  printf 'CGROUP_EVENTS\n'
  cat "$scope_directory/memory.events"
}
trap record_resources EXIT
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
    staged-r29/*) source=$stage/${relative#staged-r29/}; source_root=$stage ;;
    generated/*) source=$bundle/$relative; source_root=$bundle/generated ;;
    *) source=$bundle/$relative; source_root=$bundle/${relative%%/*} ;;
  esac
  destination=$output/${module//./\/}.olean
  mkdir -p "$(dirname "$destination")"
  printf 'START target=%s source=%s\n' "$module" "$relative"
  /usr/bin/time -f "RESULT target=$module exit=%x wall_s=%e peak_kib=%M swaps=%W" \
    /home/dombarker/.elan/bin/lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$source_root" -o "$destination" "$source"
  count=$((count + 1))
  [[ "$mode" == preflight ]] && break
done < "$bundle/R30-CLOSURE-ORDER.tsv"
if [[ "$mode" == preflight ]]; then
  printf 'PREFLIGHT target=V7CallerCurrentReleaseR26.TypesExternal modules=%s status=passed\n' "$count"
  exit 0
fi
printf 'FINAL target=V7ProductionSnapshotObserverR30ClosureAxioms modules=%s status=passed\n' "$count"
