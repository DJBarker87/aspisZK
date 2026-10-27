#!/bin/bash
set -eu
cd /home/dombarker/project-offloads/codex-pv-optb-20261027/probes/native
cc -O2 -shared -fPIC getrandom-world.c -o getrandom-world.so
for mode in malformed fixture; do
  /usr/bin/time -v -o "seed1-${mode}.time" timeout 180 env LD_PRELOAD="$PWD/getrandom-world.so" PV_SEED=1 target/release/pv-optb-failure-probe "$mode" "/home/dombarker/project-offloads/codex-pv-optb-20261027/retained-ledger-seed1-${mode}" > "seed1-${mode}.log" 2>&1
done
