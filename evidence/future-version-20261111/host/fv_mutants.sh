#!/bin/bash
# Round 7: the mutation campaign (tools/r1-cost-probe/src/bin/one_tx_mutants.rs) built in two
# source trees and run on the same recorded proofs; the two verdict files must be identical.
# Usage: fv_mutants.sh <tag> <stride> <tree-a> <tree-b> [cargo-features]
# cargo-features: a space-separated list passed to --features, e.g. the deployed feature set as
# "aspis-r1-cost-probe/future-tight-base aspis-core/future-fast-kmul ...". Without it the tool is
# built with the tool crate's own features only, and the feature-gated verifier paths are OFF.
# Time is expected in compilation (each tree has its OWN target directory, target/native-mut-<tree>,
# so that no artifact of one tree can be taken for the other's; the runs take seconds).
# The first runs of this script (tags t64, full, dep) shared one target directory between the two
# trees. Cargo may then reuse one tree's artifacts for the other, so those runs are not relied on.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
TAG=$1; STRIDE=$2; A=$3; B=$4; FEAT=${5:-}
mkdir -p mutants
D=$W/MUTANTS_$TAG.done; rm -f $D
for S in $A $B; do
  if [ ! -x $W/mutants/one_tx_mutants-$TAG-$S ]; then
    cp $W/one_tx_mutants.rs $W/$S/tools/r1-cost-probe/src/bin/one_tx_mutants.rs
    bash fv_slot.sh BM-$TAG-$S 3000 bash -c "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native-mut-$S CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 cargo +1.94.1 build --release --offline --locked --bin one_tx_mutants --features '$FEAT' && cp $W/target/native-mut-$S/release/one_tx_mutants $W/mutants/one_tx_mutants-$TAG-$S" || { echo BUILD_FAILED_$S > $D; exit 1; }
  fi
done
for S in $A $B; do
  bash fv_slot.sh MU-$TAG-$S 6000 bash -c "taskset --cpu-list 0-3 $W/mutants/one_tx_mutants-$TAG-$S $W/devnet/PIN2_TRANSACTIONS.json $W/mutants/$TAG-$S.txt $STRIDE 4" || { echo RUN_FAILED_$S > $D; exit 1; }
done
{
  sha256sum mutants/$TAG-$A.txt mutants/$TAG-$B.txt mutants/one_tx_mutants-$TAG-$A mutants/one_tx_mutants-$TAG-$B one_tx_mutants.rs
  echo "features: $FEAT"
  wc -l mutants/$TAG-$A.txt mutants/$TAG-$B.txt
  if cmp -s mutants/$TAG-$A.txt mutants/$TAG-$B.txt; then echo IDENTICAL; else echo "DIFFERENT: $(diff mutants/$TAG-$A.txt mutants/$TAG-$B.txt | grep -c '^<') lines"; diff mutants/$TAG-$A.txt mutants/$TAG-$B.txt | head -20; fi
  echo "verdict counts ($A):"; grep -v '^#' mutants/$TAG-$A.txt | awk '{print $1, $2, $(NF-1), $NF}' | sed -E 's/ [0-9]+ / /' | sort | uniq -c | sort -rn | head -40
} > $D 2>&1
