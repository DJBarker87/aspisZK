#!/bin/bash
# Round 2 measurements, cumulative: W1 = W0 + E1, W2 = W1 + E2, W3 = W2 + E3. Plain builds, six fixtures each.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
F0=private-leaf-salts,future-fast-kmul
run() { # <attempt> <features>
  bash fv_scope.sh $1 1800 bash $W/fv_build.sh $1 $2 || { echo "BUILD_FAILED $1" > $W/$DONE; exit 1; }
  for f in transfer-13 transfer-255 transfer-1023 withdrawal-13 withdrawal-255 withdrawal-1023; do bash fv_scope.sh M6-$1-$f 300 bash $W/fv_run.sh $1 $f; done
}
DONE=ALL6_DONE
run W1-e1 $F0,future-fast-prepared
run W2-e2 $F0,future-fast-prepared,future-fast-square
run W3-e3 $F0,future-fast-prepared,future-fast-square,future-validated-decode
echo done > $W/ALL6_DONE
