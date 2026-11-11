#!/bin/bash
# Local-validator rehearsal only (builds and replays done in fv_all19.sh). Usage: fv_all20.sh <name>
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1
bash fv_local_prepare.sh $N || { echo PREPARE_FAILED > $W/DONE_$N; exit 1; }
(bash fv_scope.sh V-$N 6000 bash $W/fv_local_validator.sh $N > $W/validator-$N.log 2>&1 &)
ok=0
for i in $(seq 1 60); do
  sleep 5
  curl -s -m 3 http://127.0.0.1:18957 -X POST -H 'Content-Type: application/json' -d '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' | grep -q '"ok"' && { ok=1; break; }
done
[ $ok = 1 ] || { echo VALIDATOR_NOT_HEALTHY > $W/DONE_$N; pkill -f "solana-test-validator --ledger $W/$N/ledger"; exit 1; }
bash fv_scope.sh L-$N 5400 bash $W/fv_local_run_timing.sh $N A5-onetx-lean; rc=$?
pkill -f "solana-test-validator --ledger $W/$N/ledger"
echo "local run exit $rc" > $W/DONE_$N
