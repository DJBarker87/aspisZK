#!/usr/bin/env bash
set -euo pipefail

readonly repo=${ASPIS_SOURCE_ROOT:?set ASPIS_SOURCE_ROOT to this source checkout}
readonly out=${ASPIS_AENEAS_OUTPUT:?set ASPIS_AENEAS_OUTPUT to an empty output directory}
readonly charon=${CHARON_BIN:?set CHARON_BIN to pinned Charon 0.1.223}
readonly aeneas=${AENEAS_BIN:?set AENEAS_BIN to the pinned Lean 4.32 backend}

mkdir -p "$out"
export CARGO_BUILD_JOBS=1
cd "$repo"
"$charon" cargo \
  --preset aeneas \
  --mir built \
  --sysroot default \
  --start-from aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_observe \
  --start-from aspis_core::v6_transcript::snapshot_query_batch_prechallenge \
  --dest-file "$out/V7CallerCurrentReleaseR20.llbc" \
  -- \
  --release \
  --locked \
  --package aspis-core \
  --lib \
  --features aeneas-observer

cd "$out"
"$aeneas" \
  -backend lean \
  -dest "$out" \
  -namespace V7CallerCurrentReleaseR20 \
  -split-files \
  "$out/V7CallerCurrentReleaseR20.llbc"

sha256sum "$out/V7CallerCurrentReleaseR20.llbc" "$out/Funs.lean" "$out/Types.lean"
if rg -n '\bsorry\b|\badmit\b|sorryAx|native_decide' "$out/Funs.lean" "$out/Types.lean"; then
  exit 3
fi
