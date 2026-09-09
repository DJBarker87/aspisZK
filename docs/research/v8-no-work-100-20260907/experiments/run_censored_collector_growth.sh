#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly researchpin=532ade2064e533602902fc9ae5b4dd90f9207131
readonly mathpin=81a5d257c8e410db227a6665ed08f64fea08e997
readonly mathcache="$cache/.lake/packages/mathlib"
readonly toolroot=/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0
readonly target=CensoredCollectorGrowth
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
provenance() {
  [[ "$(git -C "$mathcache" rev-parse HEAD)" == "$mathpin" ]] || exit 2
  [[ -z "$(git -C "$mathcache" status --porcelain --untracked-files=no)" ]] || exit 2
  shasum -a 256 "$cache/lean-toolchain" "$cache/lake-manifest.json" \
    "$mathcache/Mathlib/Data/Finset/Card.lean" \
    "$mathcache/.lake/build/lib/lean/Mathlib/Data/Finset/Card.olean" \
    "$toolroot/src/lean/Lean/Elab/Tactic/Omega.lean" \
    "$toolroot/lib/lean/Lean/Elab/Tactic/Omega.olean"
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
      {parent[$1]=$2;mem[$1]=$3} END {for(pid in parent){p=pid;for(n=0;n<64&&p!=0;n++){
        if(p==root){total+=mem[pid];break}p=parent[p]}} print total+0}')"
    if (( rss > 7340032 )); then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      ids="$(ps -axo pid=,ppid= | awk -v root="$timed_pid" '
        {parent[$1]=$2} END {for(pid in parent){p=pid;for(n=0;n<64&&p!=0;n++){
          if(p==root&&pid!=root){print pid;break}p=parent[p]}}}')"
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
  printf 'RESEARCH_PIN=%s\nMATHLIB_PIN=%s\n' "$researchpin" "$mathpin"
  git -C "$repo" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/$target.lean" "$ex/run_censored_collector_growth.sh"
  provenance
  printf 'COMMAND=lake env lean -M7000 -R %s -o %s/%s.olean %s/%s.lean\n' "$ex" "$ex" "$target" "$ex" "$target"
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
  provenance
} 2>&1 | tee "$log"
