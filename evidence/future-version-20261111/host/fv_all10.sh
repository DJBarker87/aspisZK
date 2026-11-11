#!/bin/bash
# Round 3, second set, cumulative from W10: + D1, + D2, + E4b. Plain builds, six fixtures each (summed path).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
F9=private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary
run() { # <attempt> <features>
  bash fv_scope.sh $1 1800 bash $W/fv_build.sh $1 $2 || { echo "BUILD_FAILED $1" > $W/ALL10_DONE; exit 1; }
  for f in transfer-13 transfer-255 transfer-1023 withdrawal-13 withdrawal-255 withdrawal-1023; do bash fv_scope.sh M10-$1-$f 300 bash $W/fv_run.sh $1 $f; done
}
run W11-d1 $F9,future-d-inactive-tensor
run W12-d2 $F9,future-d-inactive-tensor,future-d-pair-expansion
run W13-e4b $F9,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place
echo done > $W/ALL10_DONE
