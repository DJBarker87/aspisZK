#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 3 && ! -e "$2" && ( "$1" == 13 || "$1" == 255 ) && ( "$3" == transfer || "$3" == withdrawal ) ]] || { echo 'usage: script 13|255 NEW_OUTPUT transfer|withdrawal' >&2; exit 2; }
readonly count="$1" out="$2"
readonly operation="$3"
readonly svm="$ex/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection"
readonly producer="$ex/performance-host/target/release/aspis-v8-performance-host"
pool="$rt/sbf-matched-pool/aspis_v8_comparison_pool_sbf.so";registry="$rt/sbf-matched-registry/aspis_v8_comparison_registry_sbf.so"
verifier="$rt/sbf-complete/aspis_v8_complete_sbf.so";double="$rt/sbf-complete/aspis_pair_forest_result_double.so"
if [[ "${ASPIS_COMPLETE_CURRENT:-0}" == 1 ]];then
 pool="$rt/sbf-selected-pool/aspis_pool.so";registry="$rt/sbf-selected-registry/aspis_registry.so"
 verifier="$rt/sbf-complete-lazy/aspis_v8_complete_sbf.so"
 [[ "${ASPIS_COMPLETE_PARTIAL:-0}" != 1 ]] || verifier="$rt/sbf-complete-partial/aspis_v8_complete_sbf.so"
fi
mkdir "$out"
scope(){ local step="$1"; shift; systemd-run --user --scope --unit="aspis-v8-complete-$count-$step-$(date +%s)-$$" -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v env NO_DNA=1 "$@"; }
scope context env ASPIS_V8_EXPORT_CONTEXT="$out/context" "$svm" "$pool" "$verifier" "$registry" "$double" "$out/export-unused.json" "$out/no-proof-needed.bin" success 1400000 asq8 "$count" "$operation" 2>&1 | tee "$out/context.log"
scope prover env ASPIS_V8_COMPLETE_CONTEXT="$out/context" "$producer" "$out/proofs" 2>&1 | tee "$out/prover.log"
for seed in 1 2 3; do
 scope "seed-$seed" "$svm" "$pool" "$verifier" "$registry" "$double" "$out/seed-$seed.json" "$out/proofs/proof-$seed.bin" success 1400000 asq8 "$count" "$operation" 2>&1 | tee "$out/seed-$seed.log"
done
