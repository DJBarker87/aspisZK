#!/bin/bash
# Translatability pass, worker 3: the changed crates' own tests in <tree>, optimised, deployed feature sets:
# aspis-core with r0 and the four deployed kernel features, aspis-statement with r0,pool-v1-kernel and the nine
# optimized-terminal audit features. Own target directory per tree. Usage: fv_tp3_tests.sh <name> <tree>
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native-test-$S CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
SF=r0,pool-v1-kernel,pool-v1-pair-forest-packed-digest-selector-tensor-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-endpoint-selector-cache-audit,pool-v1-pair-forest-semantic-factor-audit,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-packed-range-audit,pool-v1-pair-forest-active-mask-basis-audit
CF=r0,future-fast-kmul,future-fast-prepared,future-fast-square,future-lazy-horner
bash fv_slot.sh T3-TS-$N 3000 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV cargo +1.94.1 test --release --offline --locked -p aspis-statement --lib --features $SF"
echo "statement tests exit $?" > $W/TP3TESTS_$N.done
bash fv_slot.sh T3-TC-$N 3000 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV cargo +1.94.1 test --release --offline --locked -p aspis-core --lib --features $CF"
echo "core tests exit $?" >> $W/TP3TESTS_$N.done
grep -h "^test result" receipts/T3-TS-$N/stdout.log receipts/T3-TC-$N/stdout.log >> $W/TP3TESTS_$N.done
