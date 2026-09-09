#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly researchpin=1b8f72d9de123b16eb831754e58518e66a33d3f3
readonly sourcepin=26a9cd4718aae9f9de7ef1c3394fb74a229085d5
readonly nearcache=/tmp/aspis-v8-near-gamma-cache
readonly jointcache=/tmp/aspis-v8-joint-cache.n3hmg5
readonly target=ThreeHelperSelected
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
provenance() {
  [[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
  local queue=(ThreeHelperCover FixedC1HelperReduction NearGammaSelectedCoefficients) seen=' ' n=0 module relative import source olean directory
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "
    case "$module" in
      ThreeHelperCover)
        source="$ex/ThreeHelperCover.lean"; olean="$ex/ThreeHelperCover.olean"
        [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == 83554ad47bca052f4f44656f28402c4beaa0a555b1c6d909b200556259f463e7 ]] || exit 2
        [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == d8af96cfc12e2e5e35e7bee685c35d61bae59f311cc961d50df09075851303ea ]] || exit 2 ;;
      FixedC1HelperReduction)
        source="$ex/FixedC1HelperReduction.lean"; olean="$ex/FixedC1HelperReduction.olean"
        [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == 424204c75d0a9672310030a01557ca2ebcab3915064f11a5680067bad34a682e ]] || exit 2
        [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == aca2f04d7a4751d0d13706fd90ec048f2e3082453feda13492706a8ce5e89ece ]] || exit 2 ;;
      FiniteSumConcat)
        source="$ex/FiniteSumConcat.lean"; olean="$ex/FiniteSumConcat.olean"
        [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == 85e06c9cd2d57c4e8144ed3369c5040eeef4c9b23ba4f7b47b1bfe9028fbfbfe ]] || exit 2
        [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == dae768e7bf3497611d5e8091cb98257aabb3ca38c9bf774f3007948ca3647255 ]] || exit 2 ;;
      ScalarPowerSplitInstances)
        source="$ex/ScalarPowerSplitInstances.lean"; olean="$ex/ScalarPowerSplitInstances.olean"
        [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == 040a9d48a35cce00e9a7f48a8769435e5f12c9cafbbc58fe027c036ffa034a40 ]] || exit 2
        [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == f38f142329f37a7826cfa0d00e75361effee8650c315f6a9a834f707ea1fd244 ]] || exit 2 ;;
      ScalarPowerSplit)
        source="$ex/ScalarPowerSplit.lean"; olean="$ex/ScalarPowerSplit.olean"
        [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == 13e82766de39c9cb91fa4aeae171ce6e1b2564225806f59df4e8bff9cd79a190 ]] || exit 2
        [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == 854350b9e34ebbe0e27d0e0ab53f45fd3494d8a015477b640aedec9072871d92 ]] || exit 2 ;;
      AspisFormal.*)
        relative="${module//.//}"; source="$cache/$relative.lean"
        olean="$cache/.lake/build/lib/lean/$relative.olean"
        [[ "$(git -C /Users/dominic/ZK hash-object "AspisFormal/$relative.lean")" == "$(git -C /Users/dominic/ZK rev-parse "$sourcepin:AspisFormal/$relative.lean")" ]] || exit 2 ;;
      Mathlib|Mathlib.*) continue ;;
      *)
        source="$ex/$module.lean"; olean="$ex/$module.olean"
        for directory in "$nearcache" "$jointcache"; do
          [[ -e "$olean" ]] || olean="$directory/$module.olean"
        done
        [[ "$(git -C "$repo" hash-object "$source")" == "$(git -C "$repo" rev-parse "$researchpin:docs/research/v8-no-work-100-20260907/experiments/$module.lean")" ]] || exit 2 ;;
    esac
    shasum -a 256 "$source" "$olean"
    while read -r import; do queue+=("$import"); done < <(rg '^import ' "$source" | awk '{print $2}' || true)
  done
}
bounded_leaf() {
  local leanpath timed_pid rss ids
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$ex:$nearcache:$jointcache:$leanpath" /usr/bin/time -l \
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
  printf 'RESEARCH_PIN=%s\nBORROWED_SOURCE_PIN=%s\n' "$researchpin" "$sourcepin"
  git -C "$repo" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/$target.lean" "$ex/run_three_helper_selected.sh" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
  provenance
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
  provenance
} 2>&1 | tee "$log"
