#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly researchpin=b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9
readonly sourcepin=26a9cd4718aae9f9de7ef1c3394fb74a229085d5
readonly target=MaskedCurveTail
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
provenance() {
  [[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
  [[ "$(shasum -a 256 "$cache/.lake/build/lib/lean/AspisFormal/V5FriDegreeThreeCorrelatedAgreement.olean" | awk '{print $1}')" == fb90716671c026eec8a31bd21b7e0699134ff112f186b650458d5f456abd449a ]] || exit 2
  local queue=(AspisFormal.V5FriDegreeThreeCorrelatedAgreement) seen=' ' n=0 module relative import source olean
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
      *) printf 'UNEXPECTED_IMPORT=%s\n' "$module"; exit 2 ;;
    esac
    shasum -a 256 "$source" "$olean"
    while read -r import; do queue+=("$import"); done < <(rg '^import ' "$source" | awk '{print $2}' || true)
  done
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
  shasum -a 256 "$ex/$target.lean" "$ex/run_masked_curve_tail.sh"
  before="$(provenance)"; printf '%s\n' "$before"
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
  after="$(provenance)"; printf '%s\n' "$after"
  [[ "$before" == "$after" ]] || { echo PROVENANCE_CHANGED; exit 2; }
  echo PROVENANCE_UNCHANGED=true
} 2>&1 | tee "$log"
