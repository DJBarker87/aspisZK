#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly overlay="$ex/.selected-forest-cache"
readonly pin=edb199c12fcc41f00330298b95b4736f60ac6f3a
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
check "$ex/SelectedOutputPair.lean" cdce2ed893d0d1e87ad1e838df2ea9dd9c1d19409e5053d0be6d93749616e4e1
check "$ex/SelectedOutputPair.olean" 20fec171072bb15bc8821946917fdaa81bd73fc2397d3a5c2a5786e3cb5a7208
check "$ex/SelectedOutputNotes.lean" e7a51e542c33f0c90db5330d43ad02d3dbe405e4c89cd1f01f02e30963e9b2bb
check "$ex/SelectedOutputNotes.olean" 00da269fe397e50fcefc17623ebc012a7e8fc3bd081390b67e157f861e41982a
check "$ex/SelectedNoteRecovery.lean" 0c281c1e59a538bc80c9aa88cf8d92f321b140050e9b5e410436696bc7f5a5d3
check "$ex/SelectedNoteRecovery.olean" 5fbfa077b05a1d961995621bb763973946ade7b8a10eecaed07b70013c5df33a
check "$ex/SelectedForestPath.lean" 8f0248edf14e711cc50f5038c3968ae5e90fc9b6ba01aba2e5ad94a8ece8e409
check "$ex/SelectedForestPath.olean" 771e1c180ba3345f6e4579fed3bf7b03c308dc5004effcbd46105d2100537311
check "$ex/SelectedPairDecoder.lean" 3f670127e035a4ea7f532decb2127386975d2a39e188761dcc9c3eaad55c249e
check "$ex/SelectedPairDecoder.olean" abb67f4a8ec702e4a605a7048081122e5c9ad4462a7449063761ab6aa715c6f8
check "$overlay/AspisFormal/V7PairForestGatedMerkle.olean" f832d8a65a4eae27cceb5843a46942f017dd76495e562413f51e7be9f1b138b2
check "$overlay/AspisFormal/Pool/V7PairLeafOccupancy.olean" a483f5baa7101d3c3a3ca6ceb86b7f40993f3fa4f68bfb20d372c05aa5437e6a
check "$cache/.lake/build/lib/lean/AspisFormal/HashMerkleModel.olean" 131bf128f7dd9f6f13182c6e390672d26679f3f9084fcd9598d138d17dfbc4f5
check "$cache/.lake/build/lib/lean/AspisFormal/V5AcceptedSpendRelation.olean" b8beb1c0d7150de1b1a663c43b01aaaf08d46fda93cbe4ff64531533018306f1
check "$cache/.lake/build/lib/lean/AspisFormal/ArithmetizationCore.olean" 6ab5f3738e8018b86409fd1ec394527d1e6eded5816817f11385529e0c579300
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
  case "$rel" in
    AspisFormal/V7PairForestGatedMerkle|AspisFormal/Pool/V7PairLeafOccupancy) ;;
    *) cmp "$cache/.lake/build/lib/lean/$rel.olean" "$overlay/$rel.olean";;
  esac
  shasum -a 256 "$repo/AspisFormal/$rel.lean" "$overlay/$rel.olean"
  while read -r child; do audit_imports "$child"; done < <(
    awk '$1=="import" && $2 ~ /^AspisFormal\./ {print $2}' "$repo/AspisFormal/$rel.lean")
}
bounded_leaf(){
  local leanpath pid rss ids child
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$overlay:$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$ex" -o "$ex/SelectedAppendAfterstate.olean" "$ex/SelectedAppendAfterstate.lean" & pid=$!
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
  audit_imports AspisFormal.V7PairForestGatedMerkle
  audit_imports AspisFormal.V5AcceptedSpendRelation
  audit_imports AspisFormal.Pool.V7PairLeafOccupancy
  for src in crates/aspis-statement/src/poseidon2.rs crates/aspis-statement/src/spend.rs \
    crates/aspis-statement/src/pool_v1/pair_trace.rs \
    crates/aspis-statement/src/pool_v1/format.rs crates/aspis-statement/src/pool_v1/payment_relation.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_trace.rs \
    crates/aspis-statement/src/pool_v1/pair_constraint_residuals.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs \
    crates/aspis-statement/src/pool_v1/incremental_merkle.rs \
    crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs \
    docs/research/v8-no-work-100-20260907/experiments/recovered_witness.rs; do
    [[ "$(git -C "$repo" hash-object "$src")" == "$(git -C "$repo" rev-parse "$pin:$src")" ]] || exit 2
    shasum -a 256 "$repo/$src"
  done
  for name in SelectedNoteRecovery SelectedForestPath SelectedPairDecoder SelectedOutputNotes SelectedOutputPair; do
    research_path="docs/research/v8-no-work-100-20260907/experiments/$name.lean"
    [[ "$(git -C "$repo" hash-object "$research_path")" == "$(git -C "$repo" rev-parse "$pin:$research_path")" ]] || exit 2
    shasum -a 256 "$ex/$name.lean" "$ex/$name.olean"
  done
  shasum -a 256 "$ex/SelectedAppendAfterstate.lean"
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$ex" \
    "$ex/SelectedAppendAfterstate.olean" "$ex/SelectedAppendAfterstate.lean"
  set +e; bounded_leaf; result=$?; set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/SelectedAppendAfterstate.olean"
} 2>&1 | tee "$log"
