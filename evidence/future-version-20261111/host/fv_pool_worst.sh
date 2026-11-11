#!/bin/bash
# Pool page zero check: run a one_tx_worst binary over a scenario list with ONE given Pool ELF and the
# X1 verifier ELF. Usage: fv_pool_worst.sh <attempt-tag> <tool-binary> <pool.so> <specs>
# Output pool-worst/<attempt-tag>.json. Time is expected in proving (one fixture proof per scenario,
# tens of seconds each); each LiteSVM run takes about a second.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
TAG=$1; B=$2; POOL=$3; SPECS=$4
mkdir -p pool-worst
bash fv_slot.sh PL-W-$TAG 5400 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+pool:$POOL taskset --cpu-list 0-3 $B $W/devnet/PIN2_TRANSACTIONS.json $POOL $W/pool-worst/$TAG.json '$SPECS' X1=$W/out/X1-rewrites/artifacts/aspis_r1_cost_probe_program.so"
echo "worst $TAG exit $?"
sha256sum $B $POOL pool-worst/$TAG.json
