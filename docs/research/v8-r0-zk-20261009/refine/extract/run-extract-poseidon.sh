#!/bin/sh
# run-extract.sh <scratch R> <tag> : Charon (pinned cb50ff16) then Aeneas (pinned b59d5188) on refine/writers,
# each in its own capped scope (MemoryHigh 6G / MemoryMax 8G / swap 0).
set -u
R=$1; A=$2; T=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016
rm -rf $R/extract/writers-$A; cp -r $R/in/refine/poseidon $R/extract/writers-$A
mkdir -p $R/extract/charon-$A $R/extract/aeneas-$A/generated
cd $R/extract/writers-$A && PATH=/home/dombarker/.cargo/bin:$PATH cargo generate-lockfile --offline
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  --setenv=PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin --setenv=RUSTUP_TOOLCHAIN=nightly-2026-06-01 \
  /usr/bin/time -v -o $R/extract/charon-$A/time.log timeout 1200 $T/charon-target/release/charon cargo \
  --preset aeneas --mir built --start-from crate::perm_rounds --start-from crate::full_round --start-from crate::internal_round \
  --start-from crate::leading_pair --start-from crate::pow5 --start-from crate::external_linear \
  --dest-file $R/extract/charon-$A/writers.llbc -- --lib --release --offline > $R/extract/charon-$A/charon.log 2>&1
echo "charon exit=$?"
cd $R/extract && systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /usr/bin/time -v -o $R/extract/aeneas-$A/time.log timeout 1200 $T/bin/aeneas -sequential -no-progress-bar \
  -abort-on-error -backend lean -namespace R0PoseidonCopy -dest $R/extract/aeneas-$A/generated -loops-to-rec \
  -print-unknown-externals $R/extract/charon-$A/writers.llbc > $R/extract/aeneas-$A/aeneas.log 2>&1
echo "aeneas exit=$?"
sha256sum $R/extract/writers-$A/src/lib.rs $R/extract/charon-$A/writers.llbc $R/extract/aeneas-$A/generated/Writers.lean $T/charon-target/release/charon $T/bin/aeneas
grep -hE "Elapsed|Maximum res|Swaps|Exit" $R/extract/charon-$A/time.log $R/extract/aeneas-$A/time.log
