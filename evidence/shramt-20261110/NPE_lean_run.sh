#!/bin/bash
set -u
cd "$(dirname "$0")"
T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
export LEAN_SYSROOT=$T PATH=$T/bin:/usr/bin:/bin TMPDIR=$PWD/tmp LEAN_PATH=$(cat NPE_LEAN_PATH.txt)
mkdir -p tmp
$T/bin/lean -j1 -M3000 -DmaxErrors=1000 ${1:-NPE_lean_probe.lean}
