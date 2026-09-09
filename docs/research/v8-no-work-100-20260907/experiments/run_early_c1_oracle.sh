#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly pin=bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee
readonly v7pin=26a9cd4718aae9f9de7ef1c3394fb74a229085d5
[[ $# == 2 && ! -e "$1" ]] || exit 2
readonly target="$2"
case "$target" in EarlyC1OracleMachine|EarlyC1OracleGame) ;; *) exit 2 ;; esac
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
provenance() {
  local queue=(AspisFormal.K1.V7BudgetedAdaptiveTargets)
  if [[ "$target" != EarlyC1OracleMachine ]]; then
    queue+=(AspisFormal.K1.V7Tag73K12Merkle208PrefixProjection AspisFormal.Pool.V7FixedWidth29TupleList AspisFormal.V5FriRelationCandidateBridge AspisFormal.Pool.V7MerklePrefixTargetCongruence AspisFormal.Pool.V7MerkleFirstUnresolvedBinding)
  fi
  local seen=' ' n=0 module relative import
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "; relative="${module//.//}"
    # Borrow the explicitly pinned CURRENT V7 closure, not mismatched old
    # research source paired with newer cached oleans. No workspace mutation.
    [[ "$(git -C /Users/dominic/ZK hash-object "AspisFormal/$relative.lean")" == "$(git -C /Users/dominic/ZK rev-parse "$v7pin:AspisFormal/$relative.lean")" ]] || exit 2
    shasum -a 256 "$cache/$relative.lean" "$cache/.lake/build/lib/lean/$relative.olean"
    while read -r import; do queue+=("$import"); done < <(rg '^import AspisFormal\.' "$cache/$relative.lean" | awk '{print $2}' || true)
  done
  if [[ "$target" != EarlyC1OracleMachine ]]; then
    for module in EarlyC1Support EarlyC1Arithmetic EarlyC1Projection NearGammaFibreBridge EarlyC1Identification EarlyC1InstanceTransport EarlyC1Specialization EarlyC1LateProjection AuthenticatedEarlyC1Prefix AuthenticatedEarlyC1Targets; do
      relative="docs/research/v8-no-work-100-20260907/experiments/$module.lean"
      [[ "$(git -C "$repo" hash-object "$relative")" == "$(git -C "$repo" rev-parse "$pin:$relative")" ]] || exit 2
      shasum -a 256 "$ex/$module.lean" "$ex/$module.olean"
    done
    shasum -a 256 "$ex/EarlyC1OracleMachine.lean" "$ex/EarlyC1OracleMachine.olean"
  fi
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
      {parent[$1]=$2; mem[$1]=$3} END {for(pid in parent){p=pid;for(n=0;n<64&&p!=0;n++){
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
  printf 'RESEARCH_PIN=%s\n' "$pin"
  printf 'V7_IMPORTED_CLOSURE_PIN=%s\n' "$v7pin"
  git -C "$ex" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/$target.lean" "$ex/run_early_c1_oracle.sh" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
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
