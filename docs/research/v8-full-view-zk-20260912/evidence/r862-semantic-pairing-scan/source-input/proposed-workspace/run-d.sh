#!/usr/bin/env bash
set -u
set -o pipefail
cd /home/dombarker/project-offloads/aspis-r724-h1-single-column-20261004-d
export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_PROFILE_RELEASE_OPT_LEVEL=3
export CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
BUILD_STATUS=0
cargo build -vv --offline --locked --release --jobs 1 --manifest-path Cargo.toml --bin r724_h1_projected_residual_probe > build.log 2>&1 || BUILD_STATUS=$?
echo "$BUILD_STATUS" > build.exit
if [ "$BUILD_STATUS" -ne 0 ]; then exit "$BUILD_STATUS"; fi
BIN=target/release/r724_h1_projected_residual_probe
PREFLIGHT_STATUS=0
"$BIN" shifted > shifted-preflight.log 2>&1 || PREFLIGHT_STATUS=$?
echo "$PREFLIGHT_STATUS" > shifted-preflight.exit
if [ "$PREFLIGHT_STATUS" -ne 0 ] || ! rg -q 'all_23x3=true' shifted-preflight.log; then
  echo "not-run: shifted low-constancy preflight did not pass" > matrix.exit
  exit 0
fi
MATRIX_STATUS=0
"$BIN" shifted242-matrix > matrix.log 2>&1 || MATRIX_STATUS=$?
echo "$MATRIX_STATUS" > matrix.exit
exit "$MATRIX_STATUS"
