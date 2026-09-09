#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$1" build="$(mktemp -d /tmp/aspis-pre-image-control.XXXXXX)"
# Small optimized standalone control: compilation, then 2187 fixed-word
# cases with all 31 alpha x 31 constant-final choices. No dependency build.
bounded() {
  local pid rss ids
  /usr/bin/time -l "$@" & pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$pid" '
      {parent[$1]=$2;mem[$1]=$3}END{for(i in parent){p=i;for(n=0;n<64&&p!=0;n++){
        if(p==root){total+=mem[i];break}p=parent[p]}}print total+0}')"
    if (( rss > 1048576 )); then
      echo 'AGGREGATE_RSS_STOP_1_GIB'
      ids="$(ps -axo pid=,ppid= | awk -v root="$pid" '
        {parent[$1]=$2}END{for(i in parent){p=i;for(n=0;n<64&&p!=0;n++){
          if(p==root&&i!=root){print i;break}p=parent[p]}}}')"
      while read -r child; do [[ -z "$child" ]] || kill -TERM "$child" 2>/dev/null || true; done <<< "$ids"
      wait "$pid" || true; return 137
    fi
    sleep 1
  done
  wait "$pid"
}
{
  git -C "$ex" rev-parse HEAD
  rustc --version
  shasum -a 256 "$ex/pre_image_control.rs" "$ex/run_pre_image_control.sh"
  echo 'STAGE=optimized_standalone_compilation'
  set +e
  bounded rustc --edition=2021 -O -C overflow-checks=yes "$ex/pre_image_control.rs" -o "$build/control"
  code=$?; set -e
  printf 'COMPILE_EXIT=%s\n' "$code"; [[ "$code" == 0 ]] || exit "$code"
  shasum -a 256 "$build/control"
  echo 'STAGE=exact_ternary_family_enumeration'
  set +e
  bounded "$build/control"
  code=$?; set -e
  printf 'CONTROL_EXIT=%s\n' "$code"; exit "$code"
} 2>&1 | tee "$log"
