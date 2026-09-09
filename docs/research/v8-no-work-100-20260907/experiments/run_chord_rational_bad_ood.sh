#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly researchpin=edb199c12fcc41f00330298b95b4736f60ac6f3a
readonly sourcepin=26a9cd4718aae9f9de7ef1c3394fb74a229085d5
readonly nearcache=/tmp/aspis-v8-near-gamma-cache
readonly jointcache=/tmp/aspis-v8-joint-cache.n3hmg5
readonly target=ChordRationalBadOOD
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
provenance() {
  [[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
  local queue=(ChordRationalDivisibility ChordRationalOOD) seen=' ' n=0 module relative import source olean directory expectedSource expectedOlean
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "
    expectedSource=; expectedOlean=
    case "$module" in
      ChordRationalAlgebra)
        expectedSource=0f2bbb7a656188724054046275acbf9f3836f5753293bd5718d94ae1a9bcaa34
        expectedOlean=ee9c23a28b498e497157de7385d2d2bc130c5ac9206ec6252b018d16769239d2 ;;
      ChordRationalDegree)
        expectedSource=78ec897e6940b5c5e2fb24728734b72841cf80571ea5408d49f7cb82d804a25b
        expectedOlean=53a1484ff6093794722940892b5d4c110cbb4d7fde5fe7e07008b714aa88fd2a ;;
      FourPointSubmodule)
        expectedSource=4ef195e244877b485ffb7929aa58fb85ec0512e54ed40a269dfa9e0867be4037
        expectedOlean=55163f124053b9e89f40c52c42e0269ba86446422b4b3844d2ef9e06c2f32fc6 ;;
      ChordRationalDivisibility)
        expectedSource=a44903575cbc9d2cb91c78433aec01ce10bcc39518c61c79d977e077f84b8b67
        expectedOlean=08a1779198e669674c19e83c5fdf286d78373ee1f3c982f5ecd36095d0582352 ;;
      ChordRationalOOD)
        expectedSource=f266904c89057a7afe89ad5a43b79136e4ca5e210ec891e6486aee4ef0c0abb1
        expectedOlean=0ef5aeb2fbf0622085583afb71d684db331151cd78f4faf66ffa3f37d499397b ;;
    esac
    if [[ -n "$expectedSource" ]]; then
      source="$ex/$module.lean"; olean="$ex/$module.olean"
      [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == "$expectedSource" ]] || exit 2
      [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == "$expectedOlean" ]] || exit 2
    else
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
          [[ "$(git -C "$repo" hash-object "$source")" == "$(git -C "$repo" rev-parse "$researchpin:docs/research/v8-no-work-100-20260907/experiments/$module.lean")" ]] || exit 2 ;;
      esac
    fi
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
  shasum -a 256 "$ex/$target.lean" "$ex/run_chord_rational_bad_ood.sh"
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
