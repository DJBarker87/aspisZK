#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
readonly scratch="$(mktemp -d /tmp/aspis-v8-final-transport.XXXXXX)"
# This focused macOS job has no dependency build. Limit each child CPU and
# monitor the entire child process tree; large host builds use cgroups instead.
bounded() {
  local timed_pid rss ids child
  (ulimit -t 180; /usr/bin/time -l "$@") &
  timed_pid=$!
  while kill -0 "$timed_pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$timed_pid" '
      {parent[$1]=$2;mem[$1]=$3} END {for(pid in parent){p=pid;for(n=0;n<64&&p!=0;n++){
        if(p==root){total+=mem[pid];break}p=parent[p]}} print total+0}')"
    if (( rss > 1048576 )); then
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
{
  printf 'RESEARCH_PIN=1b8f72d9de123b16eb831754e58518e66a33d3f3\n'
  git -C "$repo" rev-parse HEAD
  uname -a
  sysctl -n machdep.cpu.brand_string
  rustc --version
  shasum -a 256 "$ex/final_transport_strategy.rs" "$ex/run_final_transport_strategy.sh"
  printf 'EXPECTED_WORK=short optimized compilation, then final/state histogram backward induction; not proving or CU\n'
  printf 'RUSTC_COMMAND=rustc -O -C overflow-checks=yes final_transport_strategy.rs -o scratch/strategy\n'
  set +e
  bounded rustc -O -C overflow-checks=yes "$ex/final_transport_strategy.rs" -o "$scratch/strategy"
  result=$?
  set -e
  printf 'COMPILE_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$scratch/strategy"
  set +e
  bounded "$scratch/strategy"
  result=$?
  set -e
  printf 'STRATEGY_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/final_transport_strategy.rs" "$ex/run_final_transport_strategy.sh"
} 2>&1 | tee "$log"
