#!/usr/bin/env bash
# Reproduction recipe for the recorded route-guard stack audit.
# This is read-only ELF inspection; it does not build or replay.
set -euo pipefail
nuc=dombarker@100.108.41.90
work=/home/dombarker/project-offloads/aspis-r1-route-guard-3c79ec30f-20261015
linked=/home/dombarker/project-offloads/aspis-100bit-field-parser-candidate-20261014/cargo-target-v152/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so
measured="$work/bin-route-guard/aspis_r1_cost_probe_program.so"
log="$work/results/route-guard-replay/sbf-build.log"
out=/tmp/r1-route-guard-stack-audit-repro
local_results="$(cd "$(dirname "$0")" && pwd)"
scp "$local_results/stack-audit-route-guard.py" "$nuc:/tmp/r1_route_stack_audit.py"
scp "$local_results/scan-r10-stack-operands.py" "$nuc:/tmp/scan-r10-stack-operands.py"
ssh "$nuc" "test ! -e '$out' && python3 /tmp/r1_route_stack_audit.py '$log' '$linked' '$measured' '$out'"
ssh "$nuc" "python3 /tmp/scan-r10-stack-operands.py '$out/disassembly.txt'"
