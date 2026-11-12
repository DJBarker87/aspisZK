#!/bin/bash
# Runs INSIDE one capped scope. Usage: timing.sh <run> <rounds> <seed> <tagA> <tagB>
# Gate C: wall time of the fixture prover alone (pv_bytes_gate time: one proof per operation per call),
# the two binaries interleaved A, B, A, B, ... in the same scope, same caps, not pinned.
set -u
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite2-20261112
RUN=$1; N=$2; SEED=$3; A=$4; B=$5; O=$W/out/timing-$RUN.txt
test ! -e $O || { echo exists; exit 2; }
for i in $(seq 1 $N); do
  for t in $A $B; do
    echo "ROUND $i $t load=$(cut -d' ' -f1-3 /proc/loadavg) $(date -u +%T)" >> $O
    $W/out/$t/pv_bytes_gate time $SEED 1 | sed "s/^/$t /" >> $O || exit 1
  done
done
cat $O
