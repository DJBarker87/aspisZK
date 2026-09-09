#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly localcache="$ex/.selected-forest-cache"
readonly pin=15e73e9fdf529a0d0ab46353b98bccaf029bf4f5
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly mode="$1" log="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
readonly inherited=AspisFormal/V7PairForestGatedMerkle
check "$repo/AspisFormal/$inherited.lean" f1e40eac2a8971119e827777e0581292a11467a30f6529a08c2cebdbe08e687a
check "$cache/$inherited.lean" f1e40eac2a8971119e827777e0581292a11467a30f6529a08c2cebdbe08e687a
check "$cache/.lake/build/lib/lean/AspisFormal/HashMerkleModel.olean" 131bf128f7dd9f6f13182c6e390672d26679f3f9084fcd9598d138d17dfbc4f5
check "$cache/.lake/build/lib/lean/AspisFormal/V5AcceptedSpendRelation.olean" b8beb1c0d7150de1b1a663c43b01aaaf08d46fda93cbe4ff64531533018306f1
check "$cache/.lake/build/lib/lean/AspisFormal/ArithmetizationCore.olean" 6ab5f3738e8018b86409fd1ec394527d1e6eded5816817f11385529e0c579300
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" 9c5bf984a8c4ed7c7854d68673a37a3847ff24783554f451920d4ff95d68b97e
check "$ex/SelectedPairDecoder.lean" 3f670127e035a4ea7f532decb2127386975d2a39e188761dcc9c3eaad55c249e
check "$ex/SelectedPairDecoder.olean" abb67f4a8ec702e4a605a7048081122e5c9ad4462a7449063761ab6aa715c6f8
check "$ex/.selected-pair-cache/AspisFormal/Pool/V7PairLeafOccupancy.olean" a483f5baa7101d3c3a3ca6ceb86b7f40993f3fa4f68bfb20d372c05aa5437e6a
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
# Record every imported project source/cache pair; no dirty main source is
# admitted, and no dependency build is invoked. Direct roots have fixed olean
# hashes above; the existing cache remains the stated inherited provenance.
seen=' '
audit_imports(){
  local module="$1" sourcepath child obj
  case "$seen" in *" $module "*) return;; esac
  seen="$seen$module "
  sourcepath="${module//.//}.lean"
  [[ "$(git -C "$repo" hash-object "AspisFormal/$sourcepath")" == \
     "$(git -C "$repo" rev-parse "$pin:AspisFormal/$sourcepath")" ]] || exit 2
  cmp "$repo/AspisFormal/$sourcepath" "$cache/$sourcepath"
  shasum -a 256 "$cache/$sourcepath"
  obj="$cache/.lake/build/lib/lean/${module//.//}.olean"
  if [[ -e "$obj" ]]; then
    shasum -a 256 "$obj"
    mkdir -p "$(dirname "$localcache/${module//.//}.olean")"
    [[ -e "$localcache/${module//.//}.olean" ]] ||
      ln -s "$obj" "$localcache/${module//.//}.olean"
  fi
  while read -r child; do audit_imports "$child"; done < <(
    awk '$1=="import" && $2 ~ /^AspisFormal\./ {print $2}' "$repo/AspisFormal/$sourcepath")
}
case "$mode" in
  cache)
    [[ ! -e "$localcache/$inherited.olean" ]] || exit 2
    mkdir -p "$localcache/AspisFormal"
    source="$repo/AspisFormal/$inherited.lean"
    output="$localcache/$inherited.olean"
    leanroot="$repo/AspisFormal"
    ;;
  leaf)
    check "$localcache/$inherited.olean" f832d8a65a4eae27cceb5843a46942f017dd76495e562413f51e7be9f1b138b2
    source="$ex/SelectedForestPath.lean"
    output="$ex/SelectedForestPath.olean"
    leanroot="$ex"
    ;;
  *) exit 2 ;;
esac
bounded_leaf(){
  local leanpath timed_pid rss ids child result
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$localcache:$ex/.selected-pair-cache:$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$leanroot" -o "$output" "$source" &
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
  printf 'RESEARCH_PIN=%s\nMODE=%s\n' "$pin" "$mode"
  git -C "$repo" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  audit_imports AspisFormal.V7PairForestGatedMerkle
  audit_imports AspisFormal.V5AcceptedSpendRelation
  audit_imports AspisFormal.Pool.V7PairLeafOccupancy
  mkdir -p "$localcache/AspisFormal/Pool"
  [[ -e "$localcache/AspisFormal/Pool/V7PairLeafOccupancy.olean" ]] ||
    ln -s "$ex/.selected-pair-cache/AspisFormal/Pool/V7PairLeafOccupancy.olean" \
      "$localcache/AspisFormal/Pool/V7PairLeafOccupancy.olean"
  shasum -a 256 "$source" "$ex/SelectedPairDecoder.lean" "$ex/SelectedPairDecoder.olean"
  [[ "$mode" != leaf ]] || shasum -a 256 "$localcache/$inherited.olean"
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$leanroot" "$output" "$source"
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$output"
} 2>&1 | tee "$log"
