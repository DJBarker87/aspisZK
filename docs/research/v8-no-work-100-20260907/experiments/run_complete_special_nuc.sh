#!/usr/bin/env bash
# Changed-limit tests / instrumented complete transactions, not deployments.
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 2 && ! -e "$2" ]] || { echo 'usage: script cap1200|cap1200-partial-max|profile|rollback|rollback-partial NEW_OUTPUT' >&2; exit 2; }
readonly mode="$1" out="$2"
readonly svm="$ex/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection"
readonly pool="$rt/sbf-selected-pool/aspis_pool.so" registry="$rt/sbf-selected-registry/aspis_registry.so"
readonly double="$rt/sbf-complete/aspis_pair_forest_result_double.so"
case "$mode" in
 cap1200) verifier="$rt/sbf-complete-lazy/aspis_v8_complete_sbf.so"; limit=1200000; operations=transfer;counts=13;seeds='1 2 3';scenario=success;;
 profile) verifier="$rt/sbf-complete-profile/aspis_v8_complete_sbf.so";limit=1400000;operations='transfer withdrawal';counts='13 255';seeds=1;scenario=success;;
 rollback) verifier="$rt/sbf-complete-lazy/aspis_v8_complete_sbf.so";limit=1400000;operations=withdrawal;counts='13 255';seeds=1;scenario=withdrawal-cpi-failure;;
 cap1200-partial-max) verifier="$rt/sbf-complete-partial/aspis_v8_complete_sbf.so";limit=1200000;operations='transfer withdrawal';counts=13;seeds='1 2 3';scenario=success;;
 rollback-partial) verifier="$rt/sbf-complete-partial/aspis_v8_complete_sbf.so";limit=1400000;operations=withdrawal;counts='13 255';seeds=1;scenario=withdrawal-cpi-failure;;
 *) exit 2;;
esac
mkdir "$out"
for op in $operations;do for count in $counts;do for seed in $seeds;do
 if [[ "$op" == transfer ]];then proof="$rt/complete-transfer-$count-v1/proofs/proof-$seed.bin";
 else proof="$rt/complete-withdrawal-$count-v2/proofs/proof-$seed.bin";fi
 [[ "$mode" != cap1200-partial-max ]] || proof="$rt/complete-max-$op-$count-v1/proofs/proof-$seed.bin"
 # Keep LiteSVM's ordinary runtime configuration; enforce the lower limit in
 # TransactionConfig. The driver's diagnostic budget override also resets heap
 # policy and is NOT an appropriate way to lower only the transaction CU cap.
 systemd-run --user --scope --unit="aspis-complete-$mode-$op-$count-$seed-$(date +%s)-$$" -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v env NO_DNA=1 ASPIS_MATCHED_V7=0 ASPIS_COMPLETE_TX_LIMIT="$limit" "$svm" "$pool" "$verifier" "$registry" "$double" "$out/$op-$count-$seed.json" "$proof" "$scenario" 1400000 asq8 "$count" "$op" 2>&1 | tee "$out/$op-$count-$seed.log"
done;done;done
sha256sum "$verifier" "$pool" "$registry" "$svm" > "$out/artifact-hashes.txt"
