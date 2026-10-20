#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-cx-ids-20261020
D=/home/dombarker/project-offloads/codex-r1-format-adopt-20261019/artifacts/pool_gate_adopt
REG=/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so
for kind in transfer withdrawal; do for n in 13 255 1023; do
 L=$kind-$n; T=$H/runs/default/$L; F=$H/runs/adopt/$L/task
 mkdir -p "$T"
 "$H/harness/capped-run.sh" "cu-$L" 'saved compact fixture replay: seconds; optimized existing LiteSVM driver' "$H" -- "$D" "$H/artifacts/pool/aspis_pool.so" "$H/artifacts/default/aspis_r1_cost_probe_program.so" "$REG" "$T/evidence.json" "$T/task" "$kind" success --pairs "$n" --reuse "$F/r1-s2-proof.bin" "$F/r1-s2-public-asf8.bin" --split 10 --tx-version v1
done; done
