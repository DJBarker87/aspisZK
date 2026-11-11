#!/bin/bash
# Round 2 measurements, cumulative from W3: + E4a, + E5, + E6, + E7, + E8. Plain builds, six fixtures each.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
F3=private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode
run() { # <attempt> <features>
  bash fv_scope.sh $1 1800 bash $W/fv_build.sh $1 $2 || { echo "BUILD_FAILED $1" > $W/ALL7_DONE; exit 1; }
  for f in transfer-13 transfer-255 transfer-1023 withdrawal-13 withdrawal-255 withdrawal-1023; do bash fv_scope.sh M7-$1-$f 300 bash $W/fv_run.sh $1 $f; done
}
run W4-e4a $F3,future-merkle-single-pass
run W5-e5 $F3,future-merkle-single-pass,future-tight-base
run W6-e6 $F3,future-merkle-single-pass,future-tight-base,future-tight-ext
run W7-e7 $F3,future-merkle-single-pass,future-tight-base,future-tight-ext,future-tight-weights
run W8-e8 $F3,future-merkle-single-pass,future-tight-base,future-tight-ext,future-tight-weights,future-lazy-boundary
echo done > $W/ALL7_DONE
