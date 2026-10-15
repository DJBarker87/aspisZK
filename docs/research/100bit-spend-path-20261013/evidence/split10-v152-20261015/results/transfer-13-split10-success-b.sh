#!/usr/bin/env bash
set -euo pipefail
ulimit -c 0
w=/home/dombarker/project-offloads/aspis-r1-split10-run-20261015
p3=/home/dombarker/project-offloads/aspis-100bit-path-20261013/results/100bit-path-20261013
fixture=/home/dombarker/project-offloads/aspis-100bit-field-parser-candidate-20261014/transfer-13-os-task
stem="$w/results/transfer-13-split10-success-b-run"
task="$w/transfer-13-split10-success-b-task"
test ! -e "$task"
test ! -e "$stem.json"
export ASPIS_SOURCE_REVISION=aba310f1daa065a27da89d15c6c47166037a8a71+split10-5a91339444d14c2a9c63c9dbd22923003ebd79f63b76c97da175c2042aa62912+gate-9ba7074f21a758cb2d69d66d8323fb78c0f60a98c981efe1e9e2f7ca265fddeb
cd "$w"
exec /usr/bin/time -v -o "$stem.outer.time.log" /usr/bin/python3 /home/dombarker/project-offloads/aspis-100bit-path-20261013/scripts/v8_state_only_cu_record.py "$stem" /home/dombarker/project-offloads/aspis-100bit-field-parser-candidate-20261014/cargo-target-v152/release/pool_gate "$p3/pool-input-artifacts/aspis_pool.so" "$w/bin-split10/aspis_r1_cost_probe_program.so" "$p3/pool-input-artifacts/aspis_registry.so" "$w/results/transfer-13-split10-success-b-evidence.json" "$task" transfer success --pairs 13 --tx-version v0 --reuse "$fixture/r1-s2-proof.bin" "$fixture/r1-s2-public-asf8.bin"
