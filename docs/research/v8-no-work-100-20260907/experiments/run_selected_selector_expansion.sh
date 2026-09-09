#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly overlay="$ex/.positive-terminal-cache"
readonly pin=51b78cbf7fadee4ec70328c86add7678a43f21da
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
check "$ex/PositivePackBinding.lean" f2332636ff75ac7b397f9fabd7b6479f1df4c63bd071f14013200badd4edea69
check "$ex/PositivePackBinding.olean" 3d5b74e3208f993f5aaaa283a128ac586ff5af5e19fe63bc7017d71c8dbaa912
check "$ex/PositiveTerminalInsertion.lean" 57d294af1f91039cc397931301d9fde808d100c0297bc1511549b7880e4e0ce5
check "$ex/PositiveTerminalInsertion.olean" 36102e188126f736d09bd215528a3029e786482a651d06804a6b19c9ba5d355b
check "$overlay/AspisFormal/Pool/V7PairForestCuArithmeticEquivalences.olean" 9dc263536b9e571475209d39af6b2ff78a8942bf8c1d0f1f4792d809f4ae1edb
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" 9c5bf984a8c4ed7c7854d68673a37a3847ff24783554f451920d4ff95d68b97e
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
seen=' '
audit_imports(){
  local module="$1" rel child
  case "$seen" in *" $module "*) return;; esac
  seen="$seen$module "; rel="${module//.//}"
  [[ "$(git -C "$repo" hash-object "AspisFormal/$rel.lean")" == \
     "$(git -C "$repo" rev-parse "$pin:AspisFormal/$rel.lean")" ]] || exit 2
  cmp "$repo/AspisFormal/$rel.lean" "$cache/$rel.lean"
  shasum -a 256 "$repo/AspisFormal/$rel.lean" "$overlay/$rel.olean"
  if [[ "$rel" != AspisFormal/Pool/V7PairForestCuArithmeticEquivalences ]]; then
    cmp "$cache/.lake/build/lib/lean/$rel.olean" "$overlay/$rel.olean"
  fi
  while read -r child; do audit_imports "$child"; done < <(
    awk '$1=="import" && $2 ~ /^AspisFormal\./ {print $2}' "$repo/AspisFormal/$rel.lean")
}
bounded_leaf(){
  local leanpath pid rss ids child
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$overlay:$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$ex" -o "$ex/SelectedSelectorExpansion.olean" "$ex/SelectedSelectorExpansion.lean" & pid=$!
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
  audit_imports AspisFormal.Pool.V7PairForestCuArithmeticEquivalences
  audit_imports AspisFormal.V5ComponentCQM31TowerExact
  for src in crates/aspis-core/src/field.rs crates/aspis-statement/src/constraints_v4.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs \
    docs/research/v8-no-work-100-20260907/experiments/PositiveTerminalInsertion.lean \
    docs/research/v8-no-work-100-20260907/experiments/PositivePackBinding.lean; do
    [[ "$(git -C "$repo" hash-object "$src")" == "$(git -C "$repo" rev-parse "$pin:$src")" ]] || exit 2
    shasum -a 256 "$repo/$src"
  done
  shasum -a 256 "$ex/PositivePackBinding.olean" "$ex/PositiveTerminalInsertion.olean" \
    "$ex/SelectedSelectorExpansion.lean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$ex" \
    "$ex/SelectedSelectorExpansion.olean" "$ex/SelectedSelectorExpansion.lean"
  set +e; bounded_leaf; result=$?; set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/SelectedSelectorExpansion.olean"
} 2>&1 | tee "$log"
