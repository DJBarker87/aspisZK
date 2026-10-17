#!/usr/bin/env bash
set -euo pipefail

KIT=/home/dombarker/project-offloads/pair-forest-lane-encoder-extraction-20261017/input
OUT=/home/dombarker/project-offloads/pair-forest-lane-encoder-extraction-20261017/output
TARGET=/home/dombarker/project-offloads/pair-forest-lane-encoder-extraction-20261017/target
CARGO=/home/dombarker/.cargo/bin/cargo
CHARON=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon
AENEAS=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas
export PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin
export RUSTUP_TOOLCHAIN=nightly-2026-06-01
export CARGO_BUILD_JOBS=1
export CARGO_PROFILE_RELEASE_OPT_LEVEL=3
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
export RUSTFLAGS='-C overflow-checks=yes'
export CARGO_TARGET_DIR="$TARGET"
export CARGO_NET_OFFLINE=true
mkdir -p "$OUT/generated" "$OUT/logs"

cd "$KIT"
date -u +%FT%TZ > "$OUT/start.utc"
/usr/bin/time -v "$CARGO" build --manifest-path "$KIT/Cargo.toml" --release --offline --lib > "$OUT/logs/build.log" 2>&1
/usr/bin/time -v "$CHARON" cargo --preset aeneas --mir built --sysroot default --start-from crate::encode_lane_from_authenticated_result_v1 --dest-file "$OUT/lane-encoder.llbc" -- --manifest-path "$KIT/Cargo.toml" --release --offline --lib > "$OUT/logs/charon.log" 2>&1
/usr/bin/time -v "$AENEAS" -sequential -no-progress-bar -abort-on-error -backend lean -namespace AspisR1PairForestLaneEncoderSourceCut -dest "$OUT/generated" -subdir AspisR1PairForestLaneEncoderSourceCut -split-files -emit-json -print-unknown-externals -loops-to-rec "$OUT/lane-encoder.llbc" > "$OUT/logs/aeneas.log" 2>&1
date -u +%FT%TZ > "$OUT/finish.utc"
