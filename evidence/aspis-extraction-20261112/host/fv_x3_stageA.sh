#!/bin/bash
# X3 stage A: build the Aeneas Lean library of the pinned Aeneas commit with its own toolchain and manifest.
# Run as: nohup bash W/x3/bin/fv_x3_stageA.sh > W/x3/stageA.log 2>&1 &   (calls fv_slot.sh itself, serially:
# one slot at a time; attempt names X3-A-*). Writes W/x3/STAGEA_STATUS (running / done / failed:<step>).
# Source: W/x3/aeneas-src/backends/lean, extracted from PCWH_T004_out/aeneas-exact-source.tar.gz
#   (archive sha256 87f5f1310e5049cf2299069e6e2b7d9f30377703ea2cb5e0ba3eed3853d4e86d, the archive the binary was
#   built from per PCWH_T004 receipt.json, aeneas_revision 0d21a9ec7bbbb110110cacc14464a47fd71c8705).
# The Mathlib cache goes to W/x3/mathlib-cache (MATHLIB_CACHE_DIR), not the shared ~/.cache/mathlib.
# Floors: refuses to start under 60 GiB free; stops at any step boundary under 45 GiB free.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
X=$W/x3
B=$X/aeneas-src/backends/lean
TC=leanprover/lean4:v4.36.0-rc2
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
ST=$X/STAGEA_STATUS
fail() { echo "failed:$1" > $ST; df -BG / | tail -1 >> $X/stageA-df.txt; exit 1; }
disk() {  # $1 = label, $2 = floor GiB
  local g; g=$(df -BG --output=avail / | tail -1 | tr -dc 0-9)
  echo "$(date -u +%FT%TZ) $1 free_GiB=$g" >> $X/stageA-df.txt
  [ "$g" -ge "$2" ] || fail "disk-$1"
}
echo running > $ST
disk start 60
[ "$(cat $B/lean-toolchain)" = "$TC" ] || fail toolchain-file
sha256sum $B/lean-toolchain $B/lake-manifest.json $B/lakefile.lean > $X/stageA-inputs.sha256
du -sk $HOME/.elan/toolchains > $X/stageA-elan-before.txt
# 1. toolchain (adds one toolchain; removes nothing). A download, not a build.
s=$(date +%s); $HOME/.elan/bin/elan toolchain install $TC > $X/stageA-elan.log 2>&1 || fail elan
echo "elan_install_wall_s $(( $(date +%s)-s ))" >> $X/stageA-walls.txt
$TCD/bin/lean --version > $X/stageA-lean-version.txt; $TCD/bin/lake --version >> $X/stageA-lean-version.txt
disk after-toolchain 45
ENV="$W/slotbin/taskset --cpu-list 0-3 env PATH=$TCD/bin:/usr/bin:/bin HOME=$HOME MATHLIB_CACHE_DIR=$X/mathlib-cache LEAN_NUM_THREADS=4"
cd $B
# 2. dependencies at the manifest revisions (lake clones them from the manifest; never `lake update`) and the
#    Mathlib cache (never a cold Mathlib build)
bash $W/fv_slot.sh X3-A-cache 5400 $ENV lake exe cache get || fail cache
sha256sum -c $X/stageA-inputs.sha256 > /dev/null || fail manifest-changed
for p in .lake/packages/*; do echo "$(basename $p) $(git -C $p rev-parse HEAD)"; done > $X/stageA-package-revs.txt
disk after-cache 45
# 3. the library itself; Mathlib must come entirely from the cache
bash $W/fv_slot.sh X3-A-build 7200 $ENV lake build Aeneas AeneasMeta || fail build
disk after-build 45
du -sk .lake .lake/packages/* $X/mathlib-cache > $X/stageA-disk.txt
du -sk $HOME/.elan/toolchains > $X/stageA-elan-after.txt
echo done > $ST
