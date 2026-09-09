#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly mode="$1" out="$2"
readonly svm="$ex/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection"
verifier="$rt/sbf-complete-partial/aspis_v8_complete_sbf.so"
[[ "${ASPIS_V8_CHANNEL:-0}" != 1 ]] || verifier="$rt/sbf-complete-channel/aspis_v8_complete_sbf.so"
[[ "${ASPIS_V8_GROUP:-0}" != 1 ]] || verifier="$rt/sbf-complete-group/aspis_v8_complete_sbf.so"
[[ "${ASPIS_V8_TAG7:-0}" != 1 ]] || verifier="$rt/sbf-complete-tag7/aspis_v8_complete_sbf.so"
[[ "${ASPIS_V8_SCATTER:-0}" != 1 ]] || verifier="$rt/sbf-complete-scatter/aspis_v8_complete_sbf.so"
[[ "${ASPIS_V8_TAG_BOUNDED:-0}" != 1 ]] || verifier="$rt/sbf-complete-tag-bounded/aspis_v8_complete_sbf.so"
[[ "${ASPIS_V8_TAG_SHARED:-0}" != 1 ]] || verifier="$rt/sbf-complete-tag-shared/aspis_v8_complete_sbf.so"
[[ "${ASPIS_V8_TAG_OFFSET:-0}" != 1 ]] || verifier="$rt/sbf-complete-tag-offset/aspis_v8_complete_sbf.so"
[[ "${ASPIS_V8_GAMMA_FIXED:-0}" != 1 ]] || verifier="$rt/sbf-complete-gamma-fixed/aspis_v8_complete_sbf.so"
[[ "${ASPIS_V8_MERKLE_BOTH:-0}" != 1 ]] || verifier="$rt/sbf-complete-merkle-both/aspis_v8_complete_sbf.so"
readonly verifier registry="$rt/sbf-selected-registry/aspis_registry.so"
readonly double="$rt/sbf-complete/aspis_pair_forest_result_double.so"
case "$mode" in
 reject-old|reject-fast)
  pool="$rt/sbf-selected-pool/aspis_pool.so"
  [[ "$mode" != reject-fast ]] || pool="$rt/sbf-pool-zero-fast/aspis_pool.so"
  mkdir "$out"
  for op in transfer withdrawal;do
   proof="$rt/complete-max-$op-255-v1/proofs/proof-1.bin"
   for index in 0 1 2 3 4 5 6 7 8 15 63 64 4095 4096 8191 8192 8248 8249 8250 8251 8252 8253 8254 8255;do
    value=$((1 + index % 255))
    systemd-run --user --scope --unit="aspis-zero-$mode-$op-$index-$(date +%s)-$$" -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v env NO_DNA=1 ASPIS_MATCHED_V7=0 ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_ZERO_PAGE_INDEX="$index" ASPIS_ZERO_PAGE_BYTE="$value" "$svm" "$pool" "$verifier" "$registry" "$double" "$out/$op-$index.json" "$proof" nonzero-fresh-page 1400000 asq8 255 "$op" 2>&1 | tee "$out/$op-$index.log"
   done
  done
  sha256sum "$verifier" "$pool" "$registry" "$svm" > "$out/artifact-hashes.txt"
  exit 0;;
 profile-old|profile-fast) pool="$rt/sbf-pool-zero-$mode/aspis_pool.so";limit=1400000;operations=transfer;counts=255;seeds=1;scenario=success;;
 cap1200-max) pool="$rt/sbf-pool-zero-fast/aspis_pool.so";limit=1200000;operations='transfer withdrawal';counts='13 255';seeds='1 2 3';scenario=success;;
 rollback) pool="$rt/sbf-pool-zero-fast/aspis_pool.so";limit=1200000;operations=withdrawal;counts='13 255';seeds=1;scenario=withdrawal-cpi-failure;;
 *) exit 2;;
esac
mkdir "$out"
for op in $operations;do for count in $counts;do for seed in $seeds;do
 if [[ "$op" == transfer ]];then proof="$rt/complete-transfer-$count-v1/proofs/proof-$seed.bin";
 else proof="$rt/complete-withdrawal-$count-v2/proofs/proof-$seed.bin";fi
 [[ "$mode" != cap1200-max ]] || proof="$rt/complete-max-$op-$count-v1/proofs/proof-$seed.bin"
 systemd-run --user --scope --unit="aspis-zero-$mode-$op-$count-$seed-$(date +%s)-$$" -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v env NO_DNA=1 ASPIS_MATCHED_V7=0 ASPIS_COMPLETE_TX_LIMIT="$limit" "$svm" "$pool" "$verifier" "$registry" "$double" "$out/$op-$count-$seed.json" "$proof" "$scenario" 1400000 asq8 "$count" "$op" 2>&1 | tee "$out/$op-$count-$seed.log"
done;done;done
sha256sum "$verifier" "$pool" "$registry" "$svm" > "$out/artifact-hashes.txt"
