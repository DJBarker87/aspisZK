#!/bin/bash
# Naming-cleanup preflight (fz): compile the changed tree's configurations before the gate, in the gate's own
# target directories (so the gate reuses them). Runs INSIDE one fv_slot.sh scope. Usage: fv_fz_check.sh <part> <tree>
#   part a: verifier crate unit + integration tests (prover aspis), client configuration (r1p-check)
#   part b: program crate tests (aspis; R1 features), tool binaries (mutants with and without the observer, worst, all bins)
W=/home/dombarker/project-offloads/future-version-20261111
P=$1; S=$2
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
run() { echo "== $*"; local t0=$(date +%s); bash -c "$*"; local rc=$?; echo "== exit $rc wall $(( $(date +%s)-t0 )) s"; return $rc; }
bad=0
if [ $P = a ]; then
  run "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features 'prover aspis' --lib --no-run" || bad=1
  run "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features 'prover aspis' --test sampler_equivalence --test aspis_one_tx_statement_binding --test weights_equivalence --test pairing_equivalence --test dots_equivalence --test validated_prefix --test transport_equivalence --test domain_equivalence --test digest_schedule --no-run" || bad=1
  run "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-client-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features r1p-check --lib --no-run" || bad=1
else
  run "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-ptest-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe-program --features aspis --lib --no-run" || bad=1
  run "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-ptest-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe-program --features pool-adapter,private-leaf-salts --lib --no-run" || bad=1
  run "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-mut-$S cargo +1.94.1 build --release --offline --locked --bin one_tx_mutants --features 'aspis-r1-cost-probe/aspis aspis-r1-cost-probe/phase-observer'" || bad=1
  run "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-wc-$S cargo +1.94.1 build --release --offline --locked --bins" || bad=1
fi
echo "check $P bad=$bad"; exit $bad
