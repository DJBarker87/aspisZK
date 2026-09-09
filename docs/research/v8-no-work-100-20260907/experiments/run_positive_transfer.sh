#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly pin=33e13de4e4b8bfdef7f3f2fb2e472b34db44865e
[[ $# -ge 2 && $# -le 3 && ! -e "$2" ]] || exit 2
readonly mode="$1" log="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
case "$mode" in build) [[ $# == 2 ]] ;; honest|recipient_zero|change_zero) [[ $# == 3 ]] ;; *) exit 2 ;; esac
readonly work="${3:-$(mktemp -d /tmp/aspis-v8-positive.XXXXXX)}"
bounded(){
  local pid rss ids child result=0
  printf 'COMMAND:'; printf ' %q' "$@"; printf '\n'
  /usr/bin/time -l "$@" & pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$pid" '
      {parent[$1]=$2;mem[$1]=$3} END {for(pid in parent){p=pid;
        for(n=0;n<64&&p!=0;n++){if(p==root){total+=mem[pid];break}p=parent[p]}}
        print total+0}')"
    if (( rss > 7340032 )); then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      ids="$(ps -axo pid=,ppid= | awk -v root="$pid" '
        {parent[$1]=$2} END {for(pid in parent){p=pid;for(n=0;n<64&&p!=0;n++){
          if(p==root&&pid!=root){print pid;break}p=parent[p]}}}')"
      while read -r child; do [[ -z "$child" ]] || kill -TERM "$child" 2>/dev/null || true; done <<< "$ids"
      wait "$pid" || true; return 137
    fi
    sleep 1
  done
  wait "$pid" || result=$?
  printf 'EXIT=%s\n' "$result"; return "$result"
}
cd "$repo"
{
  printf 'PIN=%s\nMODE=%s\nWORK=%s\n' "$pin" "$mode" "$work"
  git rev-parse HEAD
  git diff --exit-code "$pin" -- crates/aspis-core crates/aspis-statement crates/aspis-prover
  rustc --version --verbose
  if [[ "$mode" == build ]]; then
    # Fresh cfg-specific HOST compilation is the expensive step. Dependencies
    # remain pinned/offline; arithmetic is optimized with overflow checks.
    shasum -a 256 "$ex"/*.rs "$ex/performance-host/Cargo.toml" "$ex/performance-host/Cargo.lock" > "$work/source.sha256"
    readonly flags='--cfg v8_payment_extraction --cfg v8_performance --cfg v8_performance_fast --cfg v8_structured --cfg v8_positive_transfer -A dead_code -A unexpected_cfgs -C overflow-checks=yes'
    bounded env RUSTFLAGS="$flags" cargo build --offline --locked --release --jobs 2 \
      --features insecure-spend-fixture,selected-v7-kernels --manifest-path "$ex/performance-host/Cargo.toml"
    cp "$ex/performance-host/target/release/aspis-v8-performance-host" "$work/positive-transfer"
    shasum -a 256 "$work/positive-transfer" > "$work/binary.sha256"
    shasum -a 256 -c "$work/source.sha256"
    cat "$work/binary.sha256"
  else
    shasum -a 256 -c "$work/source.sha256"
    shasum -a 256 -c "$work/binary.sha256"
    bounded env -u ASPIS_V8_MAX_FRONTIER_SCAN -u ASPIS_V8_COMPLETE_CONTEXT \
      ASPIS_V8_POSITIVE_CASE="$mode" "$work/positive-transfer" "$work/$mode"
  fi
} 2>&1 | tee "$log"
if [[ "$mode" == honest ]]; then
  rg -q '"accepted":true.*"stress_nonce_attempts":0' "$log"
elif [[ "$mode" != build ]]; then
  rg -q "POSITIVE_CASE case=$mode.*verifier_error=4.*complete_bad_proof=false" "$log"
fi
