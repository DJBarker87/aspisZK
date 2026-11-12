#!/bin/bash
# Runs INSIDE one capped scope. Usage: tests.sh <tag> <src-dir-name> <cpu-list> <suite>
# Existing test suites, optimized (cargo test --release), toolchain 1.94.1, offline, locked, -j 4.
# Time expected in compilation of the test binaries, then in the tests themselves.
set -u
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite2-20261112
TAG=$1; S=$2; CPUS=$3; SUITE=$4; OUT=$W/out/$TAG/tests; mkdir -p $OUT
test ! -e $OUT/$SUITE.log || { echo "exists"; exit 2; }
E=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
   CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 RUST_TEST_THREADS=4)
case $SUITE in
  core)      D=$W/$S; A=(-p aspis-core --features r0); TD=native-ws;;
  statement) D=$W/$S; A=(-p aspis-statement --features r0,pool-v1-kernel); TD=native-ws;;
  prover)    D=$W/$S; A=(-p aspis-prover --features r0,insecure-spend-fixture); TD=native-ws;;
  probe)     D=$W/$S; A=(-p aspis-r1-cost-probe --features r1p-check); TD=native-ws;;
  tool)      D=$W/$S/tools/r1-cost-probe; A=(--features r1p-check --bin devnet_spend --bin pv_bytes_gate); TD=native;;
  *) echo "unknown suite"; exit 2;;
esac
cd $D
printf '%s\n' "cargo +1.94.1 test --release --offline --locked ${A[*]} --no-fail-fast" > $OUT/$SUITE.cmd
taskset --cpu-list $CPUS env -i "${E[@]}" CARGO_TARGET_DIR=$W/target/$TAG/$TD cargo +1.94.1 test --release --offline --locked "${A[@]}" --no-fail-fast > $OUT/$SUITE.log 2> $OUT/$SUITE.err
rc=$?
grep -h '^test result' $OUT/$SUITE.log | awk '{p+=$4; f+=$6; i+=$8} END {print "passed "p" failed "f" ignored "i}' > $OUT/$SUITE.count
grep -h '^test .* FAILED\|^test .* failed' $OUT/$SUITE.log | sort > $OUT/$SUITE.failed
# every test with its outcome, sorted (for the before/after comparison by name)
grep -h '^test .* \.\.\. ' $OUT/$SUITE.log | sed 's/ \.\.\. \(ok\|FAILED\|ignored\).*/ ... \1/' | sort > $OUT/$SUITE.outcomes
echo "$SUITE exit $rc $(cat $OUT/$SUITE.count)"
exit $rc
