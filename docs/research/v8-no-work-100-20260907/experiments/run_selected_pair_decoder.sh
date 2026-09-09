#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly localcache="$ex/.selected-pair-cache"
readonly pin=5e26df14ad5fc674d5ea43d02431f1dc9ef682fa
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly mode="$1" log="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
readonly inherited=AspisFormal/Pool/V7PairLeafOccupancy
check "$repo/AspisFormal/$inherited.lean" eaf609988c11ce5feceac03a7771a143eaccbad8f1025cee0cf0be89c3b350c1
check "$cache/$inherited.lean" eaf609988c11ce5feceac03a7771a143eaccbad8f1025cee0cf0be89c3b350c1
[[ "$(git -C "$repo" hash-object "AspisFormal/$inherited.lean")" == \
   "$(git -C "$repo" rev-parse "$pin:AspisFormal/$inherited.lean")" ]] || exit 2
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" 9c5bf984a8c4ed7c7854d68673a37a3847ff24783554f451920d4ff95d68b97e
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
case "$mode" in
  cache)
    [[ ! -e "$localcache/$inherited.olean" ]] || exit 2
    mkdir -p "$localcache/AspisFormal/Pool"
    source="$repo/AspisFormal/$inherited.lean"
    output="$localcache/$inherited.olean"
    leanroot="$repo/AspisFormal"
    ;;
  leaf)
    check "$localcache/$inherited.olean" a483f5baa7101d3c3a3ca6ceb86b7f40993f3fa4f68bfb20d372c05aa5437e6a
    source="$ex/SelectedPairDecoder.lean"
    output="$ex/SelectedPairDecoder.olean"
    leanroot="$ex"
    ;;
  *) exit 2 ;;
esac
bounded_leaf() {
  local leanpath timed_pid rss ids result
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$localcache:$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$leanroot" -o "$output" "$source" &
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
  printf 'RESEARCH_PIN=%s\nMODE=%s\n' "$pin" "$mode"
  git -C "$repo" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$source" "$repo/AspisFormal/$inherited.lean" \
    "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
  [[ "$mode" != leaf ]] || shasum -a 256 "$localcache/$inherited.olean"
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$output"
} 2>&1 | tee "$log"
