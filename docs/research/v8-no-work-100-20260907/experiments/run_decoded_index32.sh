#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly overlay="$ex/.selected-forest-cache"
readonly pin=503332fbe747db381fc8ee67c4bbdd3631ec97cf
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
[[ "$(shasum -a 256 "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" | cut -d' ' -f1)" == 9c5bf984a8c4ed7c7854d68673a37a3847ff24783554f451920d4ff95d68b97e ]] || exit 2
bounded_leaf(){
  local leanpath pid rss ids child
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$overlay:$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$ex" -o "$ex/DecodedIndex32.olean" "$ex/DecodedIndex32.lean" & pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$pid" '
      {parent[$1]=$2;mem[$1]=$3} END {for(pid in parent){p=pid;
        for(n=0;n<64 && p!=0;n++){if(p==root){total+=mem[pid];break}p=parent[p]}}
        print total+0}')"
    if (( rss > 7340032 )); then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      ids="$(ps -axo pid=,ppid= | awk -v root="$pid" '
        {parent[$1]=$2} END {for(pid in parent){p=pid;for(n=0;n<64 && p!=0;n++){
          if(p==root && pid!=root){print pid;break}p=parent[p]}}}')"
      while read -r child; do [[ -z "$child" ]] || kill -TERM "$child" 2>/dev/null || true; done <<< "$ids"
      wait "$pid" || true; return 137
    fi
    sleep 1
  done
  wait "$pid"
}
cd "$cache"
{
  printf 'RESEARCH_PIN=%s\n' "$pin"
  git -C "$repo" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  printf 'IMPORTS=Mathlib only; pinned Mathlib source/olean checked\n'
  git -C "$cache/.lake/packages/mathlib" rev-parse HEAD
  shasum -a 256 "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
  shasum -a 256 "$ex/DecodedIndex32.lean"
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$ex" "$ex/DecodedIndex32.olean" "$ex/DecodedIndex32.lean"
  set +e; bounded_leaf; result=$?; set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/DecodedIndex32.olean"
} 2>&1 | tee "$log"
