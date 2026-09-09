#!/usr/bin/env bash
set -euo pipefail
umask 077
readonly root=/home/dombarker/project-offloads/aspis-v8-positive-complete-20260909
cd "$root"
readonly ex="$root/docs/research/v8-no-work-100-20260907/experiments" d="$root/docs/research/v8-positive-complete-devnet-20260909"
readonly mode="$1" case_name="${2:-honest}"
[[ "$case_name" == honest || "$case_name" == recipient_zero || "$case_name" == change_zero ]]
readonly driver="$ex/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection"
readonly pool="$root/local-artifacts/pool-checkpoint-fix.so" verifier="$root/sbf-complete-terminal-stack/aspis_v8_complete_sbf.so" registry="$root/local-artifacts/registry.so"
# The retained driver requires this unused image argument even in real-verifier scenarios.
readonly double="$root/results/v7-pair-forest-registry-v2-litesvm-20260830/artifacts/aspis_pair_forest_result_double.so"
scope(){ systemd-run --user --scope --unit="aspis-positive-$mode-$case_name-$(date +%s)" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v "$@"; }
case "$mode" in
context)
 scope env ASPIS_V8_EXPORT_CONTEXT="$root/positive-local-context" "$driver" "$pool" "$verifier" "$registry" "$double" "$d/evidence/context.json" /dev/null success 1200000 asq8 13 transfer;;
prove)
 scope env NO_DNA=1 ASPIS_V8_COMPLETE_CONTEXT="$root/positive-local-context" ASPIS_V8_POSITIVE_CASE="$case_name" "$ex/performance-host/target/release/aspis-v8-performance-host" "$root/positive-local-$case_name";;
run)
 scenario=success; [[ "$case_name" == honest ]] || scenario=proof-rejection
 scope env ASPIS_V8_POSITIVE_CASE="$case_name" "$driver" "$pool" "$verifier" "$registry" "$double" "$d/evidence/local-$case_name.json" "$root/positive-local-$case_name/proof-1.bin" "$scenario" 1200000 asq8 13 transfer;;
*) exit 2;;
esac
