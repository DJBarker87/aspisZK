#!/usr/bin/env bash
set -euo pipefail
ulimit -c 0
w=/home/dombarker/project-offloads/aspis-r1-split10-run-20261015
p3=/home/dombarker/project-offloads/aspis-100bit-path-20261013/results/100bit-path-20261013
if [[ $# != 7 ]]; then echo 'usage: gate mode label operation scenario pairs proof public' >&2; exit 64; fi
mode=$1; label=$2; operation=$3; scenario=$4; pairs=$5; proof=$6; public=$7
case "$mode" in
 split10) driver=/home/dombarker/project-offloads/aspis-100bit-field-parser-candidate-20261014/cargo-target-v152/release/pool_gate ;;
 split11) driver="$p3/p3-pool-13/bin/pool_gate" ;;
 *) echo 'mode must be split10 or split11' >&2; exit 64 ;;
esac
stem="$w/results/$label-run"
task="$w/$label-task"
evidence="$w/results/$label-evidence.json"
test ! -e "$task"
test ! -e "$stem.json"
test ! -e "$evidence"
export ASPIS_SOURCE_REVISION=aba310f1daa065a27da89d15c6c47166037a8a71+split10-5a91339444d14c2a9c63c9dbd22923003ebd79f63b76c97da175c2042aa62912+mode-$mode+case-$label
cd "$w"
exec /usr/bin/time -v -o "$stem.outer.time.log" /usr/bin/python3 /home/dombarker/project-offloads/aspis-100bit-path-20261013/scripts/v8_state_only_cu_record.py "$stem" "$driver" "$p3/pool-input-artifacts/aspis_pool.so" "$w/bin-split10/aspis_r1_cost_probe_program.so" "$p3/pool-input-artifacts/aspis_registry.so" "$evidence" "$task" "$operation" "$scenario" --pairs "$pairs" --tx-version v0 --reuse "$proof" "$public"
