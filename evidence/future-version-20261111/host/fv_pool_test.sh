#!/bin/bash
# Pool page zero check: the Pool crate's own tests (including the new differential tests) in one tree,
# optimised (`--release`), first with the deployed feature set, then with the default features.
# Usage: fv_pool_test.sh <source-dir-name>
# Time is expected in compilation (a cold native test build of the Pool and its two Aspis crates, own
# target directory per tree), then in the tests; the differential tests scan about 10^9 bytes in all.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
S=$1
FEATURES=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native-test-$S CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
bash fv_slot.sh PL-test-$S-deployed 3000 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV cargo +1.94.1 test --release --offline --locked -p aspis-pool --features $FEATURES"
echo "test deployed-features exit $?"
bash fv_slot.sh PL-test-$S-default 3000 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV cargo +1.94.1 test --release --offline --locked -p aspis-pool"
echo "test default-features exit $?"
for k in deployed default; do echo "== $k"; grep -E "^test result|FAILED|panicked" receipts/PL-test-$S-$k/stdout.log receipts/PL-test-$S-$k/stderr.log | head -20; done
