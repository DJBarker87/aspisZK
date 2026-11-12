#!/bin/bash
# X3 stage A: build the Aeneas Lean library of the pinned Aeneas commit with its own toolchain and manifest.
# NOT RUN on 2026-11-12: the host had 31 GB free, under the 60 GB floor of the task. Refuses below the floor.
# Run as: bash fv_x3_stageA.sh   (it calls fv_slot.sh itself; one slot; attempt names X3-A-*)
# Source: W/x3/aeneas-src/backends/lean, extracted from PCWH_T004_out/aeneas-exact-source.tar.gz
#   (archive sha256 87f5f1310e5049cf2299069e6e2b7d9f30377703ea2cb5e0ba3eed3853d4e86d, the archive the binary was
#   built from per PCWH_T004 receipt.json, aeneas_revision 0d21a9ec7bbbb110110cacc14464a47fd71c8705).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
B=$W/x3/aeneas-src/backends/lean
TC=leanprover/lean4:v4.36.0-rc2
free_kb=$(df --output=avail -k "$W" | tail -1)
if [ "$free_kb" -lt $((60*1024*1024)) ]; then echo "REFUSED: free $((free_kb/1024/1024)) GB < 60 GB"; exit 3; fi
[ "$(cat $B/lean-toolchain)" = "$TC" ] || { echo "toolchain file mismatch"; exit 4; }
sha256sum $B/lean-toolchain $B/lake-manifest.json $B/lakefile.lean > $W/x3/stageA-inputs.sha256
# 1. toolchain (adds one toolchain; removes nothing). Download only, so not in a slot.
~/.elan/bin/elan toolchain install $TC || exit 5
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
# 2. dependency checkouts at the manifest revisions (lake clones them from the manifest; never `lake update`,
#    which re-resolves revisions), then the Mathlib cache (never a cold Mathlib build)
cd $B
bash $W/fv_slot.sh X3-A-cache 3600 env PATH=$TCD/bin:/usr/bin:/bin lake exe cache get || exit 7
sha256sum -c $W/x3/stageA-inputs.sha256 || { echo "manifest changed"; exit 6; }
git -C $B/.lake/packages/mathlib rev-parse HEAD > $W/x3/stageA-mathlib-rev.txt
# 3. the library itself (Aeneas + AeneasMeta); a Mathlib module rebuilt here means the cache missed: stop
bash $W/fv_slot.sh X3-A-build 7200 env PATH=$TCD/bin:/usr/bin:/bin lake build Aeneas AeneasMeta || exit 8
du -sh $B/.lake > $W/x3/stageA-disk.txt
echo done
