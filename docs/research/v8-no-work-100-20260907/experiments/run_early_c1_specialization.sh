#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly pin=15e73e9fdf529a0d0ab46353b98bccaf029bf4f5
[[ ( $# == 1 || $# == 2 ) && ! -e "$1" ]] || exit 2
readonly target="${2:-EarlyC1Specialization}"
case "$target" in EarlyC1Specialization|EarlyC1InstanceTransport|EarlyC1LateProjection) ;; *) exit 2 ;; esac
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
[[ "$(shasum -a 256 "$ex/NearGammaFibreBridge.lean" | cut -d' ' -f1)" == 9e32881435cc4ce2e63ef6ebe4dc04722864f47e205c42d6930c593cd7949631 ]] || exit 2
check(){ [[ "$(shasum -a 256 "$ex/$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
check EarlyC1Projection.lean c29219e7d1f25f9ef5236fa3d85312a5e33cfbb5a53078ab14e23a4002b9728d
check EarlyC1Projection.olean 5f6485d1f9f05ca0ae53b26257dc45a294753d943fa25df6c4bdf792b0dcee14
check EarlyC1Support.lean f8d06ad65042db80ff11c7f162d5cd4a512b9a00b89c3bdbe7dedb414edf4d6d
check EarlyC1Support.olean 47157d9fa29a1d31ec97192a739bdf3b0c802b70c6636c046c840004922b758e
check EarlyC1Arithmetic.lean a8343405e09566d444890aaceb1fcbaa9d696c4a2d0672c3865a02b184739657
check EarlyC1Arithmetic.olean 4b7f1361c0c010c7441cb6ebd4e23787b9fb9ccdd451b9622806e3b765db78bb
check NearGammaFibreBridge.olean 584a64fbbdda15ca3d80c0fe45ebafc5cc1a9bd0788eb21ebc8bfb4f53eb9eef
check EarlyC1Identification.lean 32ef2238dd3375706b38142eabb036814aaedefa2efdd8a1753518e2e1efcc35
check EarlyC1Identification.olean 61baa62ab02479b9723388d086a4c33b1791afb970a28864ae1d1a65c5a1e22d
if [[ "$target" != EarlyC1InstanceTransport ]]; then
  check EarlyC1InstanceTransport.lean 2476cc09c9eabf19b0ff8fed798d997128306a67a831eb699785ecf3f9c102e1
  check EarlyC1InstanceTransport.olean 4137cb43679b6ac083f6d13f37b242745c3e793263074dd23e2470498e7fb13f
fi
if [[ "$target" == EarlyC1LateProjection ]]; then
  check EarlyC1Specialization.lean 60e666c4d32774496c4f768524e4ef097bd82e40634ce01a9ba23aa0672bb7eb
  check EarlyC1Specialization.olean 0d59fb1f577b7e63b8fa907e1616f2169350c209781b4cb710b2b8e1c29e3ab1
fi
readonly deps=(AspisFormal.Pool.V7FixedWidth29TupleList AspisFormal.V5FriRelationCandidateBridge)
bounded_leaf() {
  # Do not keep Lake's ~0.6 GiB parent live while elaborating the leaf. The
  # source leaf remains -M7000, with an independent 7 GiB aggregate-RSS stop.
  local leanpath timed_pid rss ids result
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$ex:$leanpath" /usr/bin/time -l \
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
      # Only validated descendants of this exact timed leaf are stopped.
      while read -r child; do [[ -z "$child" ]] || kill -TERM "$child" 2>/dev/null || true; done <<< "$ids"
      wait "$timed_pid" || true
      return 137
    fi
    sleep 1
  done
  wait "$timed_pid"
}
provenance() {
  [[ "$target" != EarlyC1Support && "$target" != EarlyC1Arithmetic ]] || return 0
  local queue=("${deps[@]}") seen=' ' n=0 module relative import
  while (( n < ${#queue[@]} )); do
    module="${queue[$n]}"; n=$((n+1))
    case "$seen" in *" $module "*) continue ;; esac
    seen="$seen$module "
    relative="${module//.//}"
    # Every imported Aspis source equals the immutable research pin and the
    # concurrent workspace source. Mutable K1 work is not silently imported.
    cmp -s "$repo/AspisFormal/$relative.lean" "$cache/$relative.lean" || exit 2
    [[ "$(git -C "$repo" hash-object "AspisFormal/$relative.lean")" == \
       "$(git -C "$repo" rev-parse "$pin:AspisFormal/$relative.lean")" ]] || exit 2
    shasum -a 256 "$cache/$relative.lean" "$cache/.lake/build/lib/lean/$relative.olean"
    while read -r import; do queue+=("$import"); done < <(
      rg '^import AspisFormal\.' "$repo/AspisFormal/$relative.lean" | awk '{print $2}' || true)
  done
}
cd "$cache"
{
  printf 'RESEARCH_PIN=%s\n' "$pin"
  git -C "$ex" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/$target.lean" "$ex/run_early_c1_specialization.sh" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
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
