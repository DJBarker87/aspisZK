#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal joint=/tmp/aspis-v8-joint-cache.n3hmg5
readonly pin=edb199c12fcc41f00330298b95b4736f60ac6f3a
readonly target=AdaptiveFinalPrior
readonly sourcepin=26a9cd4718aae9f9de7ef1c3394fb74a229085d5
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
provenance() {
  [[ "$(shasum -a 256 "$ex/PostQueryFunctional.lean" | awk '{print $1}')" == 123f92dbdcd2fb986d12fe2a394d7377d4304bb48714e1319e1dcf07ea8935df ]] || exit 2
  [[ "$(shasum -a 256 "$ex/PostQueryFunctional.olean" | awk '{print $1}')" == 1e4129d9a643b5812c1a64fb893a4bbccbcc45c7c28a9509ff20878ae6355294 ]] || exit 2
  local queue=(PostQueryFunctional) seen=' ' n=0 module relative import source output
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "; relative="${module//.//}"
    case "$module" in
      AspisFormal.*)
        source="$cache/$relative.lean"
        [[ "$(git -C /Users/dominic/ZK hash-object "AspisFormal/$relative.lean")" == \
           "$(git -C /Users/dominic/ZK rev-parse "$sourcepin:AspisFormal/$relative.lean")" ]] || exit 2
        output="$cache/.lake/build/lib/lean/$relative.olean" ;;
      Mathlib*) continue ;;
      *)
        source="$ex/$relative.lean"
        if [[ "$module" != PostQueryFunctional ]]; then
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
  printf 'RESEARCH_PIN=%s\nBORROWED_SOURCE_PIN=%s\n' "$pin" "$sourcepin"
  git -C "$repo" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/$target.lean" "$ex/run_adaptive_final_prior.sh"
  before_provenance="$(provenance)"; printf '%s\n' "$before_provenance"
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$ex" "$ex/$target.olean" "$ex/$target.lean"
  set +e; bounded_leaf; result=$?; set -e
  printf 'LEAN_EXIT=%s\n' "$result"; [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
  after_provenance="$(provenance)"
  [[ "$before_provenance" == "$after_provenance" ]] || { echo 'PROVENANCE_CHANGED'; exit 2; }
  echo 'PROVENANCE_UNCHANGED=true'
} 2>&1 | tee "$log"

