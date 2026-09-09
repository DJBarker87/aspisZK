#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
[[ $# == 2 && ! -e "$2" ]] || exit 2
case "$1" in controls|payment) ;; *) exit 2 ;; esac
readonly mode="$1" log="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
readonly work="$(mktemp -d /tmp/aspis-v8-early-trace.XXXXXX)"
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
  git rev-parse HEAD
  rustc --version --verbose
  printf 'MODE=%s\nWORK=%s\n' "$mode" "$work"
  shasum -a 256 "$ex/early_c1_trace.rs" "$ex/run_early_c1_trace.sh" "$ex/performance.rs" "$ex/relation_callback.rs"
  if [[ "$mode" == controls ]]; then
    bounded rustc --edition=2021 -O -C overflow-checks=yes --test "$ex/early_c1_trace.rs" -o "$work/controls"
    bounded "$work/controls" --test-threads=1 --nocapture
  else
    # One changed actual-answer instrumented host execution, not SBF/CU work.
    # Compilation is the expected expensive step; all arithmetic is release.
    # Reuse Cargo's pinned offline dependency cache, with aggregate RSS guard.
    readonly flags='--cfg v8_payment_extraction --cfg v8_performance --cfg v8_performance_fast --cfg v8_structured --cfg v8_early_prefix -A dead_code -A unexpected_cfgs -C overflow-checks=yes'
    bounded env RUSTFLAGS="$flags" cargo build --offline --locked --release --jobs 2 \
      --features insecure-spend-fixture,selected-v7-kernels --manifest-path "$ex/performance-host/Cargo.toml"
    shasum -a 256 "$ex/performance-host/target/release/aspis-v8-performance-host" "$ex/performance-host/Cargo.lock"
    bounded env -u ASPIS_V8_MAX_FRONTIER_SCAN -u ASPIS_V8_COMPLETE_CONTEXT \
      "$ex/performance-host/target/release/aspis-v8-performance-host" "$work/public-fixture"
  fi
} 2>&1 | tee "$log"
if [[ "$mode" == controls ]]; then
  rg -q 'test result: ok. 3 passed; 0 failed' "$log"
else
  rg -q 'EARLY_C1_TRACE.*accepted_openings=22.*actual_answers=true.*resolver_hash_calls=0' "$log"
  rg -q '"accepted":true' "$log"
fi
