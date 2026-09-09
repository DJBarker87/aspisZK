#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal joint=/tmp/aspis-v8-joint-cache.n3hmg5
readonly pin=bbca32e0e30be2c489c6437dd670da164e6d852f
readonly target=ReferenceIndependentRelation
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
provenance() {
  [[ "$(shasum -a 256 "$ex/RepresentedImageGame.lean" | awk '{print $1}')" == 71c93cc12d35d6ee3156e0e87872dde7b3b246b6aca58d9737579ba97cc93e5c ]] || exit 2
  [[ "$(shasum -a 256 "$ex/RepresentedImageGame.olean" | awk '{print $1}')" == f6fe69e35e1e46781d1fa78a1fccc2b3fd6aa5b86436af76159141b4ee4e8ef1 ]] || exit 2
  local queue=(RepresentedImageGame) seen=' ' n=0 module relative import source output
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "; relative="${module//.//}"
    case "$module" in
      AspisFormal.*)
        source="$repo/AspisFormal/$relative.lean"
        cmp -s "$source" "$cache/$relative.lean" || exit 2
        [[ "$(git -C "$repo" hash-object "AspisFormal/$relative.lean")" == \
           "$(git -C "$repo" rev-parse "$pin:AspisFormal/$relative.lean")" ]] || exit 2
        output="$cache/.lake/build/lib/lean/$relative.olean" ;;
      Mathlib*) continue ;;
      *)
        source="$ex/$relative.lean"
        if [[ "$module" != RepresentedImageGame ]]; then
          [[ "$(git -C "$repo" hash-object "$source")" == \
             "$(git -C "$repo" rev-parse "$pin:docs/research/v8-no-work-100-20260907/experiments/$relative.lean")" ]] || exit 2
        fi
        output="$ex/$relative.olean"
        if [[ ! -f "$output" ]]; then output="$joint/$relative.olean"; fi ;;
    esac
    shasum -a 256 "$source" "$output"
    while read -r import; do queue+=("$import"); done < <(awk '/^import / {print $2}' "$source")
  done
  shasum -a 256 "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
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
      {parent[$1]=$2;mem[$1]=$3} END {for(pid in parent){p=pid;for(n=0;n<64&&p!=0;n++){
        if(p==root){total+=mem[pid];break}p=parent[p]}}print total+0}')"
    if (( rss > 7340032 )); then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      ids="$(ps -axo pid=,ppid= | awk -v root="$timed_pid" '
        {parent[$1]=$2} END {for(pid in parent){p=pid;for(n=0;n<64&&p!=0;n++){
          if(p==root&&pid!=root){print pid;break}p=parent[p]}}}')"
      while read -r child; do [[ -z "$child" ]] || kill -TERM "$child" 2>/dev/null || true; done <<< "$ids"
      wait "$timed_pid" || true; return 137
    fi
    sleep 1
  done
  wait "$timed_pid"
}
cd "$cache"
{
  printf 'RESEARCH_PIN=%s\n' "$pin"
  git -C "$repo" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/$target.lean" "$ex/run_reference_independent_relation.sh"
  before_provenance="$(provenance)"; printf '%s\n' "$before_provenance"
  set +e; bounded_leaf; result=$?; set -e
  printf 'LEAN_EXIT=%s\n' "$result"; [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
  after_provenance="$(provenance)"
  [[ "$before_provenance" == "$after_provenance" ]] || { echo 'PROVENANCE_CHANGED'; exit 2; }
  echo 'PROVENANCE_UNCHANGED=true'
} 2>&1 | tee "$log"
