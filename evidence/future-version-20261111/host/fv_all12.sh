#!/bin/bash
# Round 3, third set, cumulative from W13: + G1 ... + G6. Plain builds, six fixtures each (summed path).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
F=private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place
n=14
for g in future-lean-parse future-lazy-horner future-word-scan future-dot-scale future-claim-rows future-fold-shared; do
  F=$F,$g; A=W$n-$(echo $g | sed 's/future-//'); n=$((n+1))
  bash fv_scope.sh $A 1800 bash $W/fv_build.sh $A $F || { echo "BUILD_FAILED $A" > $W/ALL12_DONE; exit 1; }
  for f in transfer-13 transfer-255 transfer-1023 withdrawal-13 withdrawal-255 withdrawal-1023; do bash fv_scope.sh M12-$A-$f 300 bash $W/fv_run.sh $A $f; done
done
echo done > $W/ALL12_DONE
