#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly researchpin=edb199c12fcc41f00330298b95b4736f60ac6f3a
readonly sourcepin=26a9cd4718aae9f9de7ef1c3394fb74a229085d5
readonly target=ChordRationalDivisibility
readonly chordsource=0f2bbb7a656188724054046275acbf9f3836f5753293bd5718d94ae1a9bcaa34
readonly chordolean=ee9c23a28b498e497157de7385d2d2bc130c5ac9206ec6252b018d16769239d2
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
provenance() {
  [[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
  local queue=() seen=' ' n=0 module relative source olean
  while read -r module; do queue+=("$module"); done < <(rg '^import ' "$ex/$target.lean" | awk '{print $2}')
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "
    case "$module" in
      AspisFormal.*)
        relative="${module//.//}"; source="$cache/$relative.lean"; olean="$cache/.lake/build/lib/lean/$relative.olean"
        [[ "$(git -C /Users/dominic/ZK hash-object "AspisFormal/$relative.lean")" == "$(git -C /Users/dominic/ZK rev-parse "$sourcepin:AspisFormal/$relative.lean")" ]] || exit 2 ;;
      Mathlib|Mathlib.*) continue ;;
      ChordRationalAlgebra)
        source="$ex/ChordRationalAlgebra.lean"; olean="$ex/ChordRationalAlgebra.olean"
        [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == "$chordsource" ]] || exit 2
        [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == "$chordolean" ]] || exit 2 ;;
      ChordRationalDegree)
        source="$ex/ChordRationalDegree.lean"; olean="$ex/ChordRationalDegree.olean"
        [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == 78ec897e6940b5c5e2fb24728734b72841cf80571ea5408d49f7cb82d804a25b ]] || exit 2
        [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == 53a1484ff6093794722940892b5d4c110cbb4d7fde5fe7e07008b714aa88fd2a ]] || exit 2 ;;
      FourPointSubmodule)
        source="$ex/FourPointSubmodule.lean"; olean="$ex/FourPointSubmodule.olean"
        [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == 4ef195e244877b485ffb7929aa58fb85ec0512e54ed40a269dfa9e0867be4037 ]] || exit 2
        [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == 55163f124053b9e89f40c52c42e0269ba86446422b4b3844d2ef9e06c2f32fc6 ]] || exit 2 ;;
      ExactFoldRecovery)
        source="$ex/ExactFoldRecovery.lean"; olean="$ex/ExactFoldRecovery.olean"
        [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == cec5a14467730d504a1d907a97171c629695a378266d701296c0d0206fbf64a6 ]] || exit 2
        [[ "$(shasum -a 256 "$olean" | awk '{print $1}')" == a04a1ef54343ab2b884302a71883c1f789ff9dddd9b5dbb696b43406465dc7d6 ]] || exit 2 ;;
      *) exit 2 ;;
    esac
    shasum -a 256 "$source" "$olean"
    while read -r module; do queue+=("$module"); done < <(rg '^import ' "$source" | awk '{print $2}' || true)
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
  shasum -a 256 "$ex/$target.lean" "$ex/run_chord_rational_divisibility.sh"
  provenance
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$ex" "$ex/$target.olean" "$ex/$target.lean"
  set +e
  bounded_leaf
  result=$?
  set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
  provenance
} 2>&1 | tee "$log"
