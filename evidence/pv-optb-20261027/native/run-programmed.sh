#!/bin/bash
set -eu
cd /home/dombarker/project-offloads/codex-pv-optb-20261027/probes/native
for mode in malformed fixture; do
  /usr/bin/time -v -o "programmed-${mode}.time" timeout 180 env LD_PRELOAD="$PWD/getrandom-world.so" PV_SEED=1 PV_PROGRAM_ORACLE=1 target/release/pv-optb-failure-probe "$mode" "/home/dombarker/project-offloads/codex-pv-optb-20261027/retained-ledger-programmed-${mode}" > "programmed-${mode}.log" 2>&1
done
