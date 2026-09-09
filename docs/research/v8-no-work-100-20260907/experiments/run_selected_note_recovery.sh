#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly pin=3a0b144dee108041320a23850ab4478444a74745
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
check "$ex/SelectedForestPath.lean" 8f0248edf14e711cc50f5038c3968ae5e90fc9b6ba01aba2e5ad94a8ece8e409
check "$ex/SelectedForestPath.olean" 771e1c180ba3345f6e4579fed3bf7b03c308dc5004effcbd46105d2100537311
check "$ex/SelectedPairDecoder.lean" 3f670127e035a4ea7f532decb2127386975d2a39e188761dcc9c3eaad55c249e
check "$ex/SelectedPairDecoder.olean" abb67f4a8ec702e4a605a7048081122e5c9ad4462a7449063761ab6aa715c6f8
check "$ex/.selected-forest-cache/AspisFormal/V7PairForestGatedMerkle.olean" f832d8a65a4eae27cceb5843a46942f017dd76495e562413f51e7be9f1b138b2
check "$ex/.selected-forest-cache/AspisFormal/Pool/V7PairLeafOccupancy.olean" a483f5baa7101d3c3a3ca6ceb86b7f40993f3fa4f68bfb20d372c05aa5437e6a
check "$cache/.lake/build/lib/lean/AspisFormal/HashMerkleModel.olean" 131bf128f7dd9f6f13182c6e390672d26679f3f9084fcd9598d138d17dfbc4f5
check "$cache/.lake/build/lib/lean/AspisFormal/V5AcceptedSpendRelation.olean" b8beb1c0d7150de1b1a663c43b01aaaf08d46fda93cbe4ff64531533018306f1
check "$cache/.lake/build/lib/lean/AspisFormal/ArithmetizationCore.olean" 6ab5f3738e8018b86409fd1ec394527d1e6eded5816817f11385529e0c579300
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" 9c5bf984a8c4ed7c7854d68673a37a3847ff24783554f451920d4ff95d68b97e
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
seen=' '
audit_imports(){
  local module="$1" rel child
  case "$seen" in *" $module "*) return;; esac
  seen="$seen$module "
  rel="${module//.//}"
  [[ "$(git -C "$repo" hash-object "AspisFormal/$rel.lean")" == \
     "$(git -C "$repo" rev-parse "$pin:AspisFormal/$rel.lean")" ]] || exit 2
  cmp "$repo/AspisFormal/$rel.lean" "$cache/$rel.lean"
  shasum -a 256 "$repo/AspisFormal/$rel.lean" "$ex/.selected-forest-cache/$rel.olean"
  while read -r child; do audit_imports "$child"; done < <(
    awk '$1=="import" && $2 ~ /^AspisFormal\./ {print $2}' "$repo/AspisFormal/$rel.lean")
}
bounded_leaf(){
  local leanpath timed_pid rss ids child
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$ex/.selected-forest-cache:$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$ex" -o "$ex/SelectedNoteRecovery.olean" "$ex/SelectedNoteRecovery.lean" &
  timed_pid=$!
  while kill -0 "$timed_pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$timed_pid" '
      {parent[$1]=$2;mem[$1]=$3} END {for(pid in parent){p=pid;
        for(n=0;n<64 && p!=0;n++){if(p==root){total+=mem[pid];break}p=parent[p]}}
        print total+0}')"
    if (( rss > 7340032 )); then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      ids="$(ps -axo pid=,ppid= | awk -v root="$timed_pid" '
        {parent[$1]=$2} END {for(pid in parent){p=pid;for(n=0;n<64 && p!=0;n++){
          if(p==root && pid!=root){print pid;break}p=parent[p]}}}')"
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
  git -C "$repo" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  audit_imports AspisFormal.V7PairForestGatedMerkle
  audit_imports AspisFormal.V5AcceptedSpendRelation
  audit_imports AspisFormal.Pool.V7PairLeafOccupancy
  shasum -a 256 "$ex/SelectedNoteRecovery.lean" "$ex/SelectedForestPath.lean" \
    "$ex/SelectedForestPath.olean" "$ex/SelectedPairDecoder.lean" "$ex/SelectedPairDecoder.olean"
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$ex" \
    "$ex/SelectedNoteRecovery.olean" "$ex/SelectedNoteRecovery.lean"
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/SelectedNoteRecovery.olean"
} 2>&1 | tee "$log"
