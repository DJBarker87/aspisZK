#!/bin/bash
# X1: compile a shim and its small test file (inside one fv_slot.sh scope) into W/x1/shimtest.
set -u
X=/home/dombarker/project-offloads/future-version-20261111/x1
D=$X/shimtest; mkdir -p $D/lean-src
for M in "$@"; do cp $X/bin/$M.lean $D/lean-src/; bash $X/bin/fv_x1_lean_one.sh $D $M 300; echo "$M exit $?"; done
