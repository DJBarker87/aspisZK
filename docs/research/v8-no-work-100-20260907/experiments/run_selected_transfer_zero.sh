#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly pin=bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee
[[ ( $# == 1 || $# == 2 ) && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
readonly build="${2:-$(mktemp -d /tmp/aspis-v8-transfer-zero.XXXXXX)}"
readonly rustc_bin="$(command -v rustc)"
bounded(){
  local pid rss ids child result
  printf 'COMMAND:'; printf ' %q' "$@"; printf '\n'
  /usr/bin/time -l "$@" & pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$pid" '
      {parent[$1]=$2;mem[$1]=$3} END {for(pid in parent){p=pid;
        for(n=0;n<64 && p!=0;n++){if(p==root){total+=mem[pid];break}p=parent[p]}}
        print total+0}')"
    if (( rss > 7340032 )); then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      ids="$(ps -axo pid=,ppid= | awk -v root="$pid" '
        {parent[$1]=$2} END {for(pid in parent){p=pid;for(n=0;n<64 && p!=0;n++){
          if(p==root && pid!=root){print pid;break}p=parent[p]}}}')"
      while read -r child; do [[ -z "$child" ]] || kill -TERM "$child" 2>/dev/null || true; done <<< "$ids"
      wait "$pid" || true
      return 137
    fi
    sleep 1
  done
  result=0; wait "$pid" || result=$?
  printf 'EXIT=%s\n' "$result"
  return "$result"
}
cd "$repo"
{
  printf 'PIN=%s\n' "$pin"
  git rev-parse HEAD
  git diff --exit-code "$pin" -- crates/aspis-core crates/aspis-statement
  printf 'CORE_SOURCE_TREE='; git rev-parse "$pin:crates/aspis-core/src"
  printf 'STATEMENT_SOURCE_TREE='; git rev-parse "$pin:crates/aspis-statement/src"
  printf 'BUILD=%s\n' "$build"
  "$rustc_bin" --version --verbose
  shasum -a 256 "$ex/selected_transfer_zero.rs" "$ex/recovered_witness.rs"
  # Rebuild the two small dependency-free libraries from the pinned research
  # source, not the old /tmp callback rlibs with incomplete provenance. All
  # three compilations are optimized and serial; no Cargo dependency build.
  if [[ $# == 2 ]]; then
    # Focused retry of only the changed leaf; hashes from the source-pinned v2
    # build log. Never accept unrelated /tmp libraries under a cache name.
    [[ "$(shasum -a 256 "$build/libaspis_core.rlib" | cut -d' ' -f1)" == 18425b7b28369a4b5f3005cd4b22a1897d870e0fe23aef6122f94e8c99040f2b ]]
    [[ "$(shasum -a 256 "$build/libaspis_statement.rlib" | cut -d' ' -f1)" == bbbb9333a8d05aae1b881e498110e43c55858598740757ff75a4519ab33d04f5 ]]
    printf 'REUSED_PINNED_V2_RLIBS=true\n'
  else
  bounded "$rustc_bin" --edition=2021 -O crates/aspis-core/build.rs -o "$build/circle-tables-generator"
  bounded env OUT_DIR="$build" "$build/circle-tables-generator"
  shasum -a 256 crates/aspis-core/build.rs "$build/circle_tables.rs"
  bounded env OUT_DIR="$build" "$rustc_bin" --edition=2021 -O --crate-name aspis_core --crate-type rlib \
    --cfg 'feature="v7-gamma-four-slot-block-audit"' \
    crates/aspis-core/src/lib.rs -o "$build/libaspis_core.rlib"
  cfgs=(spend-dynamic-rate512 pool-v1-kernel
    pool-v1-pair-forest-packed-digest-audit
    pool-v1-pair-forest-packed-digest-selector-tensor-audit
    pool-v1-pair-forest-binary-copy-weights-audit
    pool-v1-pair-forest-endpoint-selector-cache-audit
    pool-v1-pair-forest-semantic-factor-audit
    pool-v1-pair-forest-pattern-window-audit
    pool-v1-pair-forest-copy-pattern-basis-audit
    pool-v1-pair-forest-copy-selector-tensor-basis-audit
    pool-v1-pair-forest-copy-tag-dot-basis-audit
    pool-v1-pair-forest-copy-finish-dot-basis-audit
    pool-v1-pair-forest-packed-range-audit
    pool-v1-pair-forest-active-mask-basis-audit)
  args=(); for feature in "${cfgs[@]}"; do args+=(--cfg "feature=\"$feature\""); done
  bounded "$rustc_bin" --edition=2021 -O --crate-name aspis_statement --crate-type rlib \
    "${args[@]}" --extern "aspis_core=$build/libaspis_core.rlib" -L "dependency=$build" \
    crates/aspis-statement/src/lib.rs -o "$build/libaspis_statement.rlib"
  fi
  bounded "$rustc_bin" --edition=2021 -O -C overflow-checks=yes -A dead_code \
    "$ex/selected_transfer_zero.rs" --extern "aspis_core=$build/libaspis_core.rlib" \
    --extern "aspis_statement=$build/libaspis_statement.rlib" -L "dependency=$build" \
    -o "$build/selected-transfer-zero"
  bounded "$build/selected-transfer-zero"
  shasum -a 256 "$build/libaspis_core.rlib" "$build/libaspis_statement.rlib" "$build/selected-transfer-zero"
} 2>&1 | tee "$log"
