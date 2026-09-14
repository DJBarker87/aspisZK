#!/bin/sh
set -eu

: "${LEAN_BIN:?set LEAN_BIN to the pinned Lean 4.32.0 executable}"
: "${LEAN_PATH:?set LEAN_PATH to the pinned dependency search path}"

repo_root=${1:-$(git rev-parse --show-toplevel)}
source_dir="$repo_root/docs/research/v8-completion-fs-extraction-20260911/lean"
build_dir=${S7_BUILD_DIR:-$(mktemp -d)}

mkdir -p "$build_dir"

for module in \
  FSV8S7DynamicSelectedRoot \
  FSV8S7DynamicSuccessfulCut \
  FSV8S7SelectedSourcePrefixBudget \
  FSV8S7CompactWordTargetInclusion
do
  env LEAN_PATH="$build_dir:$LEAN_PATH" "$LEAN_BIN" \
    -o "$build_dir/$module.olean" "$source_dir/$module.lean"
done

env LEAN_PATH="$build_dir:$LEAN_PATH" "$LEAN_BIN" "$source_dir/FSV8S7Audit.lean"

printf '%s\n' "S7 focused Lean checks passed; artifacts: $build_dir"
