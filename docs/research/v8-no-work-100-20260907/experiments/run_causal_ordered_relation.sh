#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal joint=/tmp/aspis-v8-joint-cache.n3hmg5
readonly pin=15e73e9fdf529a0d0ab46353b98bccaf029bf4f5
readonly target=CausalOrderedRelation
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || { echo "Provenance mismatch: $1"; exit 2; }; }
check "$ex/FirstImageDiscrepancy.lean" ef2d19ab25ae7b2d6795067b95b678253bed446004cb8541c0188893c69d7230
check "$ex/FirstImageDiscrepancy.olean" a6152344385cb7bfe633674d48c4217725ad07427c37eca6497706179567c1ab
check "$ex/OrderedQueryGame.lean" 05b7d763b6fe7b123134e720b9bc370da3eed07762f7217578b37cbbce754d7e
check "$ex/OrderedQueryGame.olean" 0038965f44136724073d6584d559eb42f58761a5f5914f565d7e31610a648e52
check "$ex/OrderedPostQueryGame.lean" 45e2e9393c592a371d332f7d8b601d4a757173a00a801dba1f2426eaa5d53b5b
check "$ex/OrderedPostQueryGame.olean" 7978e927d7c28e8ec0a5f8ccd94f0fe0e4f0870b3f5ec8e5d16aa1e0b6fb836a
check "$ex/RobustImageGame.lean" b377c2c0530357f921343d8fe95f3672c28014a1808653262a06b8274cc92090
check "$ex/RobustImageGame.olean" 75c4bf0d1149d666fd9d9113567a1ff4b67d850c061826888b01a5a79db552e1
check "$ex/PostQueryFunctional.lean" 123f92dbdcd2fb986d12fe2a394d7377d4304bb48714e1319e1dcf07ea8935df
check "$ex/PostQueryFunctional.olean" 1e4129d9a643b5812c1a64fb893a4bbccbcc45c7c28a9509ff20878ae6355294
check "$ex/OptimizedRelationRefinement.lean" 98b861e3d8a4d06d2a9ffc01bb394314353dc3dbbf55efeaa4f7390d8d8e8304
check "$ex/OptimizedRelationRefinement.olean" 4aaf5ff39ddecd665d0593d57f8459c629a7cb3ee7c873798af80aac4cd4941d
check "$ex/ImageCallbackInterfaces.lean" 5d6d1f5be0a0351c1288c975355f944a9ea447d90c8c40d0b57898138ec6cdd8
check "$ex/ImageCallbackInterfaces.olean" 33b837a6e80e0697281a0195ea87dc5419852b91653523503e228cd79d2535b5
check "$ex/JointImageGame.lean" 746b466d3b5c258be8e8670e4cac47771e4dcd9223bc5828f5d803ab72fb8c1d
check "$joint/JointImageGame.olean" 4eda76950026ee3690bb26984f5ae8e59cdf3d87c9ccb8a94439cb4d1be0c780
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean" 55ee2345729e8a4d379de3bce14ea18b14fbfdc259cf2653fadf4bf3a46876d8
provenance() {
  local queue=(AspisFormal.V6RelationFold AspisFormal.V6TranscriptRelationGrammar AspisFormal.V7ExactOneFoldDomains AspisFormal.V5FriConcreteEncoderApplicability) seen=' ' n=0 module relative import
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "
    relative="${module//.//}"
    cmp -s "$repo/AspisFormal/$relative.lean" "$cache/$relative.lean" || exit 2
    [[ "$(git -C "$repo" hash-object "AspisFormal/$relative.lean")" == \
       "$(git -C "$repo" rev-parse "$pin:AspisFormal/$relative.lean")" ]] || exit 2
    shasum -a 256 "$cache/$relative.lean" "$cache/.lake/build/lib/lean/$relative.olean"
    while read -r import; do queue+=("$import"); done < <(
      rg '^import AspisFormal\.' "$repo/AspisFormal/$relative.lean" | awk '{print $2}' || true)
  done
  shasum -a 256 "$ex/FirstImageDiscrepancy.lean" "$ex/FirstImageDiscrepancy.olean" \
    "$ex/OrderedQueryGame.lean" "$ex/OrderedQueryGame.olean" \
    "$ex/OrderedPostQueryGame.lean" "$ex/OrderedPostQueryGame.olean" \
    "$ex/RobustImageGame.lean" "$ex/RobustImageGame.olean" \
    "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Fintype/CardEmbedding.olean"
  shasum -a 256 "$ex/PostQueryFunctional.lean" "$ex/PostQueryFunctional.olean" \
    "$ex/OptimizedRelationRefinement.lean" "$ex/OptimizedRelationRefinement.olean" \
    "$ex/ImageCallbackInterfaces.lean" "$ex/ImageCallbackInterfaces.olean" \
    "$ex/JointImageGame.lean" "$joint/JointImageGame.olean"
}
bounded_leaf() {
  local leanpath timed_pid rss ids
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$ex:$joint:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$ex" -o "$ex/$target.olean" "$ex/$target.lean" &
  timed_pid=$!
  while kill -0 "$timed_pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$timed_pid" '
      {parent[$1]=$2; mem[$1]=$3} END {
        for (pid in parent) {p=pid; for (n=0;n<64 && p!=0;n++) {
          if (p==root) {total+=mem[pid];break} p=parent[p]
        }} print total+0}')"
    if (( rss > 7340032 )); then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      ids="$(ps -axo pid=,ppid= | awk -v root="$timed_pid" '
        {parent[$1]=$2} END {for(pid in parent) {p=pid;for(n=0;n<64 && p!=0;n++) {
          if(p==root && pid!=root){print pid;break}p=parent[p]
        }}}')"
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
  git -C "$ex" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/$target.lean" "$ex/run_causal_ordered_relation.sh"
  before_provenance="$(provenance)"
  printf '%s\n' "$before_provenance"
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
  after_provenance="$(provenance)"
  [[ "$before_provenance" == "$after_provenance" ]] || { echo 'PROVENANCE_CHANGED'; exit 2; }
  echo 'PROVENANCE_UNCHANGED=true'
} 2>&1 | tee "$log"
