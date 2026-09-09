#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly pin=3a0b144dee108041320a23850ab4478444a74745
[[ $# == 2 && ! -e "$2" ]] || exit 2
case "$1" in NaturalProjectionCore|NaturalChordProjection) ;; *) exit 2 ;; esac
readonly target="$1" log="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
provenance() {
  local queue=(AspisFormal.V5FriConcreteEncoderApplicability) seen=' ' n=0 module relative import
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "
    relative="${module//.//}"
    cmp -s "$repo/AspisFormal/$relative.lean" "$cache/$relative.lean" || exit 2
    [[ "$(git -C "$repo" hash-object "AspisFormal/$relative.lean")" == \
       "$(git -C "$repo" rev-parse "$pin:AspisFormal/$relative.lean")" ]] || exit 2
    shasum -a 256 "$cache/$relative.lean" "$cache/.lake/build/lib/lean/$relative.olean"
    while read -r import; do queue+=("$import"); done < <(
      rg '^import AspisFormal\.' "$repo/AspisFormal/$relative.lean" | awk '{print $2}' || true)
  done
  if [[ "$target" == NaturalChordProjection ]]; then
    for module in ChordPolynomialImage NaturalLineBoundary NaturalChordImage NaturalProjectionCore; do
      shasum -a 256 "$ex/$module.lean" "$ex/$module.olean"
    done
  fi
  shasum -a 256 "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
}
bounded_leaf() {
  local leanpath timed_pid rss ids
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$ex" -o "$ex/$target.olean" "$ex/$target.lean" &
  timed_pid=$!
  while kill -0 "$timed_pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$timed_pid" '
      {parent[$1]=$2; mem[$1]=$3} END {
        for (pid in parent) {p=pid; for (n=0;n<64 && p!=0;n++) {
          if (p==root) {total+=mem[pid];break} p=parent[p]
        }} print total+0}')"
    if (( rss > 7340032 )); then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      ids="$(ps -axo pid=,ppid= | awk -v root="$timed_pid" '
        {parent[$1]=$2} END {for(pid in parent) {p=pid;for(n=0;n<64 && p!=0;n++) {
          if(p==root && pid!=root){print pid;break}p=parent[p]
        }}}')"
      while read -r child; do [[ -z "$child" ]] || kill -TERM "$child" 2>/dev/null || true; done <<< "$ids"
      wait "$timed_pid" || true
      return 137
    fi
    sleep 1
  done
  wait "$timed_pid"
}
cd "$cache"
{
  printf 'RESEARCH_PIN=%s\n' "$pin"
  git -C "$ex" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/$target.lean" "$ex/run_natural_chord_projection.sh"
  before_provenance="$(provenance)"
  printf '%s\n' "$before_provenance"
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
  after_provenance="$(provenance)"
  [[ "$before_provenance" == "$after_provenance" ]] || { echo 'PROVENANCE_CHANGED'; exit 2; }
  echo 'PROVENANCE_UNCHANGED=true'
} 2>&1 | tee "$log"
