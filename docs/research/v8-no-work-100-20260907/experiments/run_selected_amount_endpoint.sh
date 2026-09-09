#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly overlay="$ex/.positive-terminal-cache"
readonly pin=1b8f72d9de123b16eb831754e58518e66a33d3f3
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
check "$ex/SelectedSparseMle.lean" 91f8204107e4caea36f4948f3e27ae270f65413fca01b68ea1ac8ee286fbaaaa
check "$ex/SelectedSparseMle.olean" 5b9379efb68f86aff60f54fe0eb125d0fe17071fe1238318ab887e14f023594c
check "$ex/SelectedSelectorExpansion.lean" 3f6c969a075d37f46d2a93c844191dc7dbb9c974c5413bfdf0a73c92ea50999a
check "$ex/SelectedSelectorExpansion.olean" 358d9a496a1e56d9b508cf9fa726d8f597e8a6db6626fe05cb982c6236e256cb
check "$ex/PositivePackBinding.lean" f2332636ff75ac7b397f9fabd7b6479f1df4c63bd071f14013200badd4edea69
check "$ex/PositivePackBinding.olean" 3d5b74e3208f993f5aaaa283a128ac586ff5af5e19fe63bc7017d71c8dbaa912
check "$ex/PositiveTerminalInsertion.lean" 57d294af1f91039cc397931301d9fde808d100c0297bc1511549b7880e4e0ce5
check "$ex/PositiveTerminalInsertion.olean" 36102e188126f736d09bd215528a3029e786482a651d06804a6b19c9ba5d355b
check "$ex/SelectedTransferPositive.lean" 00f427ff1d17f2b01a7fbb7f18a4bc68b9814d804a05242f0ac34a5d6a9ff48f
check "$ex/SelectedTransferPositive.olean" 775b0b9796a0b206c279209742bb6a9fdfceb73428f3fe7f5087702bea19b560
check "$ex/SelectedPaymentRecovery.lean" 4c8ba95e27ed5e50e1927b6e9233b9f387b8674f5ca059949f8cd04ca7a63c18
check "$ex/SelectedPaymentRecovery.olean" ee2166caaf0ff244add6113c14b19fd8622c00fbd87607b195063b42323e3ac0
check "$overlay/AspisFormal/Pool/V7PairForestCuArithmeticEquivalences.olean" 9dc263536b9e571475209d39af6b2ff78a8942bf8c1d0f1f4792d809f4ae1edb
check "$cache/.lake/build/lib/lean/AspisFormal/ArithmetizationCore.olean" 6ab5f3738e8018b86409fd1ec394527d1e6eded5816817f11385529e0c579300
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" 9c5bf984a8c4ed7c7854d68673a37a3847ff24783554f451920d4ff95d68b97e
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
seen=' '
audit_imports(){
  local module="$1" rel child binary
  case "$seen" in *" $module "*) return;; esac
  seen="$seen$module "; rel="${module//.//}"
  [[ "$(git -C "$repo" hash-object "AspisFormal/$rel.lean")" == \
     "$(git -C "$repo" rev-parse "$pin:AspisFormal/$rel.lean")" ]] || exit 2
  cmp "$repo/AspisFormal/$rel.lean" "$cache/$rel.lean"
  binary="$cache/.lake/build/lib/lean/$rel.olean"
  if [[ -e "$overlay/$rel.olean" ]]; then
    binary="$overlay/$rel.olean"
    if [[ "$rel" != AspisFormal/Pool/V7PairForestCuArithmeticEquivalences ]]; then
      cmp "$cache/.lake/build/lib/lean/$rel.olean" "$binary"
    fi
  else
    # Lean resolves the namespace root as a unit; it does not fall back to
    # main for individual missing modules within this overlay. Reuse only
    # the existing binary after the pinned source comparison above.
    printf 'CACHE_REUSE_COPY=%s\n' "$rel"
    cp -n "$binary" "$overlay/$rel.olean"
    cmp "$binary" "$overlay/$rel.olean"
    binary="$overlay/$rel.olean"
  fi
  shasum -a 256 "$repo/AspisFormal/$rel.lean" "$binary"
  while read -r child; do audit_imports "$child"; done < <(
    awk '$1=="import" && $2 ~ /^AspisFormal\./ {print $2}' "$repo/AspisFormal/$rel.lean")
}
bounded_leaf(){
  local leanpath pid rss ids child
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$overlay:$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$ex" -o "$ex/SelectedAmountEndpoint.olean" "$ex/SelectedAmountEndpoint.lean" & pid=$!
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
  audit_imports AspisFormal.ArithmetizationCore
  for src in crates/aspis-core/src/field.rs crates/aspis-core/src/v6_transcript.rs \
    crates/aspis-statement/src/constraints_v4.rs crates/aspis-statement/src/pool_v1/pair_trace.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_trace.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_constraint_residuals.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs; do
    [[ "$(git -C "$repo" hash-object "$src")" == "$(git -C "$repo" rev-parse "$pin:$src")" ]] || exit 2
    shasum -a 256 "$repo/$src"
  done
  for name in SelectedSparseMle SelectedSelectorExpansion PositivePackBinding \
    PositiveTerminalInsertion SelectedTransferPositive SelectedPaymentRecovery; do
    readonly_path="docs/research/v8-no-work-100-20260907/experiments/$name.lean"
    [[ "$(git -C "$repo" hash-object "$readonly_path")" == "$(git -C "$repo" rev-parse "$pin:$readonly_path")" ]] || exit 2
    shasum -a 256 "$ex/$name.lean" "$ex/$name.olean"
  done
  for name in positive_transfer recovered_witness payment_extraction; do
    readonly_path="docs/research/v8-no-work-100-20260907/experiments/$name.rs"
    [[ "$(git -C "$repo" hash-object "$readonly_path")" == "$(git -C "$repo" rev-parse "$pin:$readonly_path")" ]] || exit 2
    shasum -a 256 "$repo/$readonly_path"
  done
  shasum -a 256 "$ex/SelectedAmountEndpoint.lean"
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$ex" \
    "$ex/SelectedAmountEndpoint.olean" "$ex/SelectedAmountEndpoint.lean"
  set +e; bounded_leaf; result=$?; set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/SelectedAmountEndpoint.olean"
} 2>&1 | tee "$log"
