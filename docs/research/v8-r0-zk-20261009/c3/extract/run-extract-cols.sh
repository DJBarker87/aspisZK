#!/bin/sh
# c3/extract/run-extract-cols.sh <tag> : D72.2 column writers.  run-extract-build.sh (D64) in the
# branch workspace codex-r1p-column-writers-20261019: Charon (pinned cb50ff16) then Aeneas (pinned
# b59d5188) on c3/build with builders 5 and 6 appended, each in its own capped scope
# (MemoryHigh 6G / MemoryMax 8G / swap 0).  Start points: the four extracted builders plus
# fill_round and fill_gbat.
set -u
A=$1; S=/home/dombarker/project-offloads/codex-r1p-column-writers-20261019
T=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016
R=$S/repo/docs/research/v8-r0-zk-20261009/c3
rm -rf $S/extract/build-$A; mkdir -p $S/extract; cp -r $R/build $S/extract/build-$A
mkdir -p $S/extract/charon-$A $S/extract/aeneas-$A/generated
cd $S/extract/build-$A && PATH=/home/dombarker/.cargo/bin:$PATH cargo generate-lockfile --offline
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  --setenv=PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin --setenv=RUSTUP_TOOLCHAIN=nightly-2026-06-01 \
  /usr/bin/time -v -o $S/extract/charon-$A/time.log timeout 1200 $T/charon-target/release/charon cargo \
  --preset aeneas --mir built --start-from crate::fill_tq --start-from crate::fill_lo --start-from crate::fill_own --start-from crate::fill_rel \
  --start-from crate::fill_round --start-from crate::fill_gbat \
  --dest-file $S/extract/charon-$A/build.llbc -- --lib --release --offline > $S/extract/charon-$A/charon.log 2>&1
echo "charon exit=$?"
cd $S/extract && systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /usr/bin/time -v -o $S/extract/aeneas-$A/time.log timeout 1200 $T/bin/aeneas -sequential -no-progress-bar \
  -abort-on-error -backend lean -namespace R1CertBuild -dest $S/extract/aeneas-$A/generated -loops-to-rec \
  -print-unknown-externals $S/extract/charon-$A/build.llbc > $S/extract/aeneas-$A/aeneas.log 2>&1
echo "aeneas exit=$?"
sha256sum $S/extract/build-$A/src/lib.rs $S/extract/charon-$A/build.llbc $S/extract/aeneas-$A/generated/*.lean $T/charon-target/release/charon $T/bin/aeneas
grep -hE "Elapsed|Maximum res|Swaps|Exit" $S/extract/charon-$A/time.log $S/extract/aeneas-$A/time.log
