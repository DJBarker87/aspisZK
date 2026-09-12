#!/usr/bin/env bash
set -euo pipefail

# Rebuild the focused source IR.  The caller supplies the pinned Charon and
# Aeneas binaries because those tools are intentionally not vendored here.
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
OUT=${FORMAL_REPLAY_OUT:?set FORMAL_REPLAY_OUT to an empty output directory}
SOURCE=${ASPIS_SOURCE_ROOT:?set ASPIS_SOURCE_ROOT to the pinned repository}
CHARON_BIN=${CHARON_BIN:?set CHARON_BIN to the pinned Charon binary}
AENEAS_BIN=${AENEAS_BIN:?set AENEAS_BIN to the pinned Aeneas binary}

test -d "$SOURCE/.git"
test "$(git -C "$SOURCE" rev-parse HEAD)" = \
  ccc19c1cecfaf2526edd3d3a5277c7b54b0a77bf
test "$(sha256sum "$SOURCE/crates/aspis-core/src/sumcheck.rs" | awk '{print $1}')" = \
  766f2cc4bed632819b548d8c5f516ad8e14f45df28446669c1783515511a4a47
mkdir -p "$OUT"
test -z "$(find "$OUT" -mindepth 1 -maxdepth 1 -print -quit)"

export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$OUT/cargo-target"
(cd "$SOURCE" && "$CHARON_BIN" cargo --preset aeneas --mir built \
  --sysroot default \
  --start-from 'aspis_core::sumcheck::_::weight_at' \
  --include aspis_core \
  --dest-file "$OUT/V7WeightAtStandalone.llbc" \
  -- --locked --package aspis-verifier --lib --no-default-features \
  --features v7-production-tag73)

"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error \
  -loops-no-rec -backend lean -namespace V7WeightAtStandalone \
  -dest "$OUT/generated" -subdir V7WeightAtStandalone -split-files \
  -emit-json "$OUT/V7WeightAtStandalone.llbc"

sha256sum "$OUT/V7WeightAtStandalone.llbc"
