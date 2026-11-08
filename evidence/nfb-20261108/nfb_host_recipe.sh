#!/bin/sh
# Host recipe (NOT RUN). Compiles NFB_NMFBHost in the NNH run-5 workspace on the build host,
# reusing its pinned objects; one focused scope under the standard caps. Expected time: one
# focused import elaboration (seconds); no aggregation, no export, no manifest replay.
#   B=/home/dombarker/project-offloads/codex-cx-integrate-20261111
#   T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
# Preconditions: NNH_R4_objects contains NNH_HostNativeHeader, NNH_HostRecorderEvent,
# NNH_HostClockFinding, NNH_NMFPrime, NNH_G1aEnv and TAS_TopB (all built through L842).
set -eu
B=${B:?}; T=${T:?}
cd "$B"
cp NFB_BinderGroup.lean NFB_NMFB.lean NFB_NMFBHost.lean NNH_generated/
LP="$B/NNH_R4_objects:$B/NNH_objects:$B/NNH_seed:$B/NNH_library_seed"
for m in NFB_NMFB NFB_NMFBHost; do
  systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
    env LEAN_SYSROOT="$T" LEAN_PATH="$LP" /usr/bin/time -v \
    "$T/bin/lake" env lean -j1 -M7000 -DElab.async=false -R NNH_generated \
      -o "NNH_R4_objects/$m.olean" "NNH_generated/$m.lean"
done
# Record: exact target, exit, wall, peak RSS, swaps, source revision, printed axioms (AGENTS 6).
