#!/bin/sh
# c3/extract/run-extract.sh <tag> : Charon (pinned cb50ff16) then Aeneas (pinned b59d5188) on c3/check,
# each in its own capped scope (MemoryHigh 6G / MemoryMax 8G / swap 0).  Recipe and pins from
# codex/r0-builder-model-20261019 refine/extract/run-extract.sh (read only).
set -u
A=$1; S=/home/dombarker/project-offloads/aspis-r0-checker-extract-20261019
T=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016
R=$S/repo/docs/research/v8-r0-zk-20261009/c3
rm -rf $S/extract/check-$A; mkdir -p $S/extract; cp -r $R/check $S/extract/check-$A
mkdir -p $S/extract/charon-$A $S/extract/aeneas-$A/generated
cd $S/extract/check-$A && PATH=/home/dombarker/.cargo/bin:$PATH cargo generate-lockfile --offline
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  --setenv=PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin --setenv=RUSTUP_TOOLCHAIN=nightly-2026-06-01 \
  /usr/bin/time -v -o $S/extract/charon-$A/time.log timeout 1200 $T/charon-target/release/charon cargo \
  --preset aeneas --mir built --start-from crate::check \
  --dest-file $S/extract/charon-$A/check.llbc -- --lib --release --offline > $S/extract/charon-$A/charon.log 2>&1
echo "charon exit=$?"
cd $S/extract && systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /usr/bin/time -v -o $S/extract/aeneas-$A/time.log timeout 1200 $T/bin/aeneas -sequential -no-progress-bar \
  -abort-on-error -backend lean -namespace R1CertCheck -dest $S/extract/aeneas-$A/generated -loops-to-rec \
  -print-unknown-externals $S/extract/charon-$A/check.llbc > $S/extract/aeneas-$A/aeneas.log 2>&1
echo "aeneas exit=$?"
sha256sum $S/extract/check-$A/src/lib.rs $S/extract/charon-$A/check.llbc $S/extract/aeneas-$A/generated/*.lean $T/charon-target/release/charon $T/bin/aeneas
grep -hE "Elapsed|Maximum res|Swaps|Exit" $S/extract/charon-$A/time.log $S/extract/aeneas-$A/time.log
