#!/bin/bash
# Runs INSIDE a scope. Usage: fv_run.sh <elf-attempt> <fixture>
set -u
W=/home/dombarker/project-offloads/future-version-20261111
E=$1; F=$2
FX=$W/src/docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/$F
mkdir -p $W/measurements
ASPIS_SOURCE_REVISION=$(cat $W/SOURCE_REVISION) $W/target/native/release/fused_probe $W/out/$E/artifacts/aspis_r1_cost_probe_program.so $FX/r1-s2-proof.bin $FX/r1-s2-public-asf8.bin $W/measurements/$E-$F.json $F
