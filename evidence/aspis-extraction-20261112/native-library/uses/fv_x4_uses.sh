#!/bin/bash
# Runs INSIDE one fv_slot.sh scope. Aspis port preparation: list what the Aspis model chain uses from gate-carrier
# modules of the two-transaction proof. One Lean run (Lean 4.32.0, the coherent chain objects of replay-c1 and the
# L187 objects by reference; nothing is written outside $W/x4). Time is expected in loading the import closure.
W=/home/dombarker/project-offloads/future-version-20261111
SYS=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
L=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
cd $W/x4 && sha256sum AspisChainUses.lean && env PATH=/usr/bin:/bin LEAN_SYSROOT=$SYS LEAN_PATH=$W/replay-c1/out:$L/objs:$L/base_ref timeout 1500 $SYS/bin/lean -j1 -M7000 -DElab.async=false AspisChainUses.lean
rc=$?; echo "lean exit $rc"; wc -l uses_raw.tsv 2>/dev/null; echo $rc > $W/x4/exit
