#!/bin/sh
# NPI_ one step per invocation, run inside a capped systemd scope by the caller. argv: step (test|audit)
set -u
W=/home/dombarker/project-offloads/codex-cx-trust-20261110; R=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
mkdir -p $W/tmp $W/test $W/run
export PATH=/usr/bin:/bin LEAN_SYSROOT=$T TMPDIR=$W/tmp
case "$1" in
 test) cd $W/test; cp $W/NPI_cone_union.txt $W/NPI_targets.txt $W/NPI_roots.txt $W/test/
   export LEAN_PATH=$T/lib/lean
   /usr/bin/time -v -o test.time timeout 300 $T/bin/lean -j1 -M7000 -DElab.async=false $W/NPI_AuditTest.lean > test.log 2>&1; echo exit=$? >> test.log;;
 audit) cd $W/run; cp $W/NPI_cone_union.txt $W/NPI_targets.txt $W/NPI_roots.txt $W/run/
   export LEAN_PATH=$R/final/objs:$R/objs:$R/base_ref
   /usr/bin/time -v -o audit.time timeout 900 $T/bin/lean -j1 -M7000 -DElab.async=false $W/NPI_Audit.lean > audit.log 2>&1; echo exit=$? >> audit.log;;
esac
