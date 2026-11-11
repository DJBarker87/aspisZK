#!/bin/bash
# Devnet preparation, second pass: client build and tests, replay of the recorded devnet
# settlements against the lean adapter A5, then the full rehearsal on a local validator
# (deploy --final, preflight, two one-transaction payments with negatives, cleanup).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=${1:-local1}
bash fv_scope.sh C2-client 3000 bash $W/fv_client_build.sh || { echo CLIENT_BUILD_FAILED > $W/ALL19_DONE; exit 1; }
mkdir -p replays-v3
for op in transfer withdrawal; do
  bash fv_scope.sh R6-A5-$op 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION) $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/devnet/verifier-pin2.so $W/out/A5-onetx-lean/artifacts/aspis_r1_cost_probe_program.so $op $W/replays-v3/A5-onetx-lean-$op.json" || { echo REPLAY_FAILED_$op > $W/ALL19_DONE; exit 1; }
done
bash fv_local_prepare.sh $N || { echo PREPARE_FAILED > $W/ALL19_DONE; exit 1; }
(bash fv_scope.sh V-$N 6000 bash $W/fv_local_validator.sh $N > $W/validator-$N.log 2>&1 &)
ok=0
for i in $(seq 1 60); do
  sleep 5
  curl -s -m 3 http://127.0.0.1:18957 -X POST -H 'Content-Type: application/json' -d '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' | grep -q '"ok"' && { ok=1; break; }
done
[ $ok = 1 ] || { echo VALIDATOR_NOT_HEALTHY > $W/ALL19_DONE; pkill -f "solana-test-validator --ledger $W/$N/ledger"; exit 1; }
bash fv_scope.sh L-$N 5400 bash $W/fv_local_run.sh $N A5-onetx-lean; rc=$?
pkill -f "solana-test-validator --ledger $W/$N/ledger"
echo "local run exit $rc" > $W/ALL19_DONE
