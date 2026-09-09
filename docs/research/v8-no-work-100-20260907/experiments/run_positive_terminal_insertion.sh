#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly localcache="$ex/.positive-terminal-cache"
readonly pin=33e13de4e4b8bfdef7f3f2fb2e472b34db44865e
readonly inherited=AspisFormal/Pool/V7PairForestCuArithmeticEquivalences
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly mode="$1" log="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
check "$repo/AspisFormal/$inherited.lean" 82a71be6d1942b449b58c1fd6e6e0dfa988ba2f987e9d5afd00120d562c3fc65
check "$cache/AspisFormal/V5ComponentCQM31TowerExact.lean" 75404d16b5a71f67146b91ca35739b111f81bb730beb77432267f2b5385cebe5
check "$cache/.lake/build/lib/lean/AspisFormal/V5ComponentCQM31TowerExact.olean" 5d0e1ba16ff7cc29fca900249aa75b0011402cd4b84b8766aaf8346d854d04e9
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" 9c5bf984a8c4ed7c7854d68673a37a3847ff24783554f451920d4ff95d68b97e
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
case "$mode" in
  cache)
    [[ ! -e "$localcache/$inherited.olean" ]] || exit 2
    mkdir -p "$localcache/AspisFormal/Pool"
    source="$repo/AspisFormal/$inherited.lean"
    output="$localcache/$inherited.olean"
    leanroot="$repo/AspisFormal";;
  leaf)
    check "$localcache/$inherited.olean" 9dc263536b9e571475209d39af6b2ff78a8942bf8c1d0f1f4792d809f4ae1edb
    source="$ex/PositiveTerminalInsertion.lean"
    output="$ex/PositiveTerminalInsertion.olean"
    leanroot="$ex";;
  *) exit 2;;
esac
seen=' '
audit_imports(){
  local module="$1" rel child
  case "$seen" in *" $module "*) return;; esac
  seen="$seen$module "; rel="${module//.//}"
  [[ "$(git -C "$repo" hash-object "AspisFormal/$rel.lean")" == \
     "$(git -C "$repo" rev-parse "$pin:AspisFormal/$rel.lean")" ]] || exit 2
  cmp "$repo/AspisFormal/$rel.lean" "$cache/$rel.lean"
  shasum -a 256 "$repo/AspisFormal/$rel.lean"
  if [[ "$rel" != "$inherited" ]]; then
    shasum -a 256 "$cache/.lake/build/lib/lean/$rel.olean"
    # Lean selects one AspisFormal namespace root. Reuse, do not rebuild,
    # every audited dependency in the research-only overlay.
    mkdir -p "$(dirname "$localcache/$rel.olean")"
    if [[ ! -e "$localcache/$rel.olean" ]]; then
      ln -s "$cache/.lake/build/lib/lean/$rel.olean" "$localcache/$rel.olean"
    fi
    cmp "$cache/.lake/build/lib/lean/$rel.olean" "$localcache/$rel.olean"
  fi
  while read -r child; do audit_imports "$child"; done < <(
    awk '$1=="import" && $2 ~ /^AspisFormal\./ {print $2}' "$repo/AspisFormal/$rel.lean")
}
bounded_leaf(){
  local leanpath pid rss ids child
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$localcache:$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$leanroot" -o "$output" "$source" & pid=$!
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
  printf 'RESEARCH_PIN=%s\nMODE=%s\n' "$pin" "$mode"
  git -C "$repo" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  audit_imports AspisFormal.Pool.V7PairForestCuArithmeticEquivalences
  if [[ "$mode" == leaf ]]; then
    audit_imports AspisFormal.V5ComponentCQM31TowerExact
    shasum -a 256 "$localcache/$inherited.olean"
  fi
  shasum -a 256 "$source" "$ex/positive_transfer.rs" \
    "$repo/crates/aspis-core/src/field.rs" \
    "$repo/crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs"
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$leanroot" "$output" "$source"
  set +e; bounded_leaf; result=$?; set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$output"
} 2>&1 | tee "$log"
