#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly researchpin=edb199c12fcc41f00330298b95b4736f60ac6f3a
readonly sourcepin=26a9cd4718aae9f9de7ef1c3394fb74a229085d5
readonly nearcache=/tmp/aspis-v8-near-gamma-cache
readonly jointcache=/tmp/aspis-v8-joint-cache.n3hmg5
[[ $# == 1 ]] || exit 2
readonly target=RelationCompatibleMoment
[[ ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
provenance() {
  [[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
  [[ "$(shasum -a 256 "$ex/CausalOrderedRelation.olean" | awk '{print $1}')" == a28c6b032e56c2e581dc3e14c043698f2451256298ae77ac1cfaadceba8e44db ]] || exit 2
  local queue=() seen=' ' n=0 module relative import source olean directory expected
  while read -r import; do queue+=("$import"); done < <(rg '^import ' "$ex/$target.lean" | awk '{print $2}')
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
        for directory in "$nearcache" "$jointcache"; do
          [[ -e "$olean" ]] || olean="$directory/$module.olean"
        done
        if git -C "$repo" cat-file -e "$researchpin:docs/research/v8-no-work-100-20260907/experiments/$module.lean" 2>/dev/null; then
          [[ "$(git -C "$repo" hash-object "$source")" == "$(git -C "$repo" rev-parse "$researchpin:docs/research/v8-no-work-100-20260907/experiments/$module.lean")" ]] || exit 2
        else
          for file in "$source" "$olean"; do
            expected="$(awk -v path="$file" '$2==path {print $1}' "$ex/helper-joint-pinned.sha256")"
            [[ -n "$expected" && "$(shasum -a 256 "$file" | awk '{print $1}')" == "$expected" ]] || exit 2
          done
        fi ;;
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
  shasum -a 256 "$ex/$target.lean" "$ex/run_relation_compatible_moment.sh" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
  before_provenance="$(provenance)"; printf '%s\n' "$before_provenance"
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
  after_provenance="$(provenance)"
  [[ "$before_provenance" == "$after_provenance" ]] || { echo PROVENANCE_CHANGED; exit 2; }
  echo PROVENANCE_UNCHANGED=true
} 2>&1 | tee "$log"
