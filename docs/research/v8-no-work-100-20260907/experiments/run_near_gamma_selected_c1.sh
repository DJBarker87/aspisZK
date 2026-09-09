#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly researchpin=51b78cbf7fadee4ec70328c86add7678a43f21da
readonly sourcepin=26a9cd4718aae9f9de7ef1c3394fb74a229085d5
readonly nearcache=/tmp/aspis-v8-near-gamma-cache
readonly jointcache=/tmp/aspis-v8-joint-cache.n3hmg5
[[ $# == 2 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
readonly target="$2"
case "$target" in NearGammaMessageCover|NearGammaSelectedC1|NearGammaSelectedCoefficients) ;; *) exit 2 ;; esac
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
check_old_cache() {
  local module="$1" expected="$2" directory="$3"
  [[ "$(shasum -a 256 "$directory/$module.olean" | awk '{print $1}')" == "$expected" ]] || exit 2
  shasum -a 256 "$directory/$module.olean"
}
provenance() {
  check_old_cache NearGammaSupport c053bc825124a58cbf650373eb8bab59aeef6dfa942c27ced31c63cd056ea6b3 "$nearcache"
  check_old_cache NearGammaCover acc5be5c1a673e25e1a09a50f77b65258921c2248d45844729604a689fffbd34 "$nearcache"
  check_old_cache NearGammaOwnSupport ea30125723013a668e5d8adde093f3f2887c85d7bce1a0f7866657d9f21bd55b "$nearcache"
  check_old_cache NearGammaArithmetic ab6b1e709126f8f47dceb4181cdddd9060275763321b05c0b351958ce25e1dbb "$nearcache"
  check_old_cache NearGammaDichotomy 30bf2d300135a692eccf26d27eec0aa978abb713004d2a83635ab662451a0d3a "$nearcache"
  check_old_cache JointImageGame 4eda76950026ee3690bb26984f5ae8e59cdf3d87c9ccb8a94439cb4d1be0c780 "$jointcache"
  local queue=(NearGammaDichotomy EarlyC1Support) seen=' ' n=0 module relative import source olean
  if [[ "$target" != NearGammaMessageCover ]]; then
    queue+=(EarlyC1LateProjection AspisFormal.K1.V7ExactCorrelatedAgreement)
    [[ "$(shasum -a 256 "$ex/NearGammaMessageCover.lean" | awk '{print $1}')" == adccfea2cd5fc04d76c35da41eac5b6dbf2a6d97e95adc4a3d3b79713fc51983 ]] || exit 2
    [[ "$(shasum -a 256 "$ex/NearGammaMessageCover.olean" | awk '{print $1}')" == 3724783c5e212f9f8f62558706661f41232e6cbe13ec906f89b6a50e11eb4b96 ]] || exit 2
    shasum -a 256 "$ex/NearGammaMessageCover.lean" "$ex/NearGammaMessageCover.olean"
  fi
  if [[ "$target" == NearGammaSelectedCoefficients ]]; then
    queue+=(PartialFoldRecovery)
    [[ "$(shasum -a 256 "$ex/NearGammaSelectedC1.lean" | awk '{print $1}')" == 625bd68d1d317ba0738144c6428ebc2773e8ad351791910916349af98d7c2779 ]] || exit 2
    [[ "$(shasum -a 256 "$ex/NearGammaSelectedC1.olean" | awk '{print $1}')" == d4c9935d545bd2c0ec80bd9c2542f0a53d3f2fc88b2e267abfaa5e3a64000857 ]] || exit 2
    shasum -a 256 "$ex/NearGammaSelectedC1.lean" "$ex/NearGammaSelectedC1.olean"
  fi
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "
    case "$module" in
      AspisFormal.*)
        relative="${module//.//}"; source="$cache/$relative.lean"
        olean="$cache/.lake/build/lib/lean/$relative.olean"
        [[ "$(git -C /Users/dominic/ZK hash-object "AspisFormal/$relative.lean")" == "$(git -C /Users/dominic/ZK rev-parse "$sourcepin:AspisFormal/$relative.lean")" ]] || exit 2 ;;
      Mathlib|Mathlib.*) continue ;;
      *)
        source="$ex/$module.lean"; olean="$ex/$module.olean"
        [[ -e "$olean" ]] || olean="$nearcache/$module.olean"
        [[ -e "$olean" ]] || olean="$jointcache/$module.olean"
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
  shasum -a 256 "$ex/$target.lean" "$ex/run_near_gamma_selected_c1.sh" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
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
