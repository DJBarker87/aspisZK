#!/bin/bash
# Runs INSIDE a scope. Usage: fv_trace.sh <elf-attempt> <fixture> <tag> [third-account-prefix-file]
# Traces one measurement instruction of the stripped ELF of <elf-attempt> and
# profiles it against that attempt's unstripped ELF (out/<attempt>/linked-unstripped.so).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
E=$1; F=$2; TAG=$3; EXTRA=${4:-}
FX=$W/src/docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/$F
T=$W/traces/$E-$F-tag$TAG
mkdir -p $W/profiles
test ! -e $T || { echo "trace exists"; exit 2; }
OUT=$($W/target/trace/release/aspis-fused-trace $W/out/$E/artifacts/aspis_r1_cost_probe_program.so $FX/r1-s2-proof.bin $FX/r1-s2-public-asf8.bin $TAG $T $EXTRA) || exit 1
echo "$OUT"
CU=$(echo "$OUT" | sed -n 's/.*program CU Some(\([0-9]*\)).*/\1/p')
ls -la $T | head -20
REGS=$(ls -S $T/*.regs | head -1)
python3 $W/fv_profile.py $W/out/$E/linked-unstripped.so $REGS $CU $W/profiles/$E-$F-tag$TAG.json
rc=$?
# Traces are large and rebuildable; keep only the profile.
rm -rf $T
exit $rc
