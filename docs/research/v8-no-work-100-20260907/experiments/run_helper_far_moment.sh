#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
readonly builddir="$(mktemp -d /tmp/aspis-helper-far.XXXXXX)"
bounded() {
  local pid rss children
  (ulimit -t 90; /usr/bin/time -l "$@") & pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$pid" '{parent[$1]=$2;mem[$1]=$3} END {for(pid in parent){p=pid;for(n=0;n<64&&p!=0;n++){if(p==root){total+=mem[pid];break}p=parent[p]}} print total+0}')"
    if ((rss>1048576));then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      children="$(ps -axo pid=,ppid= | awk -v root="$pid" '{parent[$1]=$2} END {for(pid in parent){p=pid;for(n=0;n<64&&p!=0;n++){if(p==root&&pid!=root){print pid;break}p=parent[p]}}}')"
      while read -r child;do [[ -z "$child" ]]||kill -TERM "$child" 2>/dev/null||true;done <<<"$children"
      wait "$pid"||true;return 137
    fi
    sleep 1
  done
  wait "$pid"
}
{
  git -C "$repo" rev-parse HEAD
  rustc --version
  [[ "$(shasum -a 256 "$ex/helper_ood_strategy.rs" | awk '{print $1}')" == 322056c4ceba5ae1c18391386ade43b50695cb4ecc2a839a0eac8ad6069da9db ]] || exit 2
  shasum -a 256 "$ex/helper_ood_strategy.rs"
  shasum -a 256 "$ex/helper_far_moment.rs" "$ex/run_helper_far_moment.sh"
  printf 'SCOPE=optimized compile plus exact full causal average within the declared restricted F19 family; 23328 prefixes; expected compute 30-60s; no QM31 or payment extrapolation\nBUILD_DIRECTORY=%s\n' "$builddir"
  set +e
  bounded rustc --edition=2021 -O -C overflow-checks=yes "$ex/helper_far_moment.rs" -o "$builddir/helper_far_moment"
  build=$?;printf 'BUILD_EXIT=%s\n' "$build";[[ "$build" == 0 ]]||exit "$build"
  bounded "$builddir/helper_far_moment" --full-causal
  run=$?;printf 'SEARCH_EXIT=%s\n' "$run";exit "$run"
} 2>&1 | tee "$log"

