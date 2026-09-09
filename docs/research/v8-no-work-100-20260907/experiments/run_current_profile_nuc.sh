#!/usr/bin/env bash
# Four deterministic maximum-body seed1 profiles; NOT a quiet-ELF CU control.
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly out="$1" svm="$ex/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection"
readonly verifier="$rt/sbf-complete-line-norm-profile/aspis_v8_complete_sbf.so"
readonly pool="$rt/sbf-pool-zero-fast/aspis_pool.so" registry="$rt/sbf-selected-registry/aspis_registry.so"
readonly double="$rt/sbf-complete/aspis_pair_forest_result_double.so"
[[ "${ASPIS_TOKEN_CONTROL:-}" == legacy35 && -d "${ASPIS_TOKEN_ELF_DIR:-}" ]] || exit 2
mkdir "$out"
for op in transfer withdrawal;do for count in 13 255;do
 proof="$rt/complete-max-$op-$count-v1/proofs/proof-1.bin"
 systemd-run --user --scope --unit="aspis-line-profile-$op-$count-$(date +%s)-$$" -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v env NO_DNA=1 ASPIS_MATCHED_V7=0 ASPIS_COMPLETE_TX_LIMIT=1200000 "$svm" "$pool" "$verifier" "$registry" "$double" "$out/$op-$count.json" "$proof" success 1400000 asq8 "$count" "$op" 2>&1 | tee "$out/$op-$count.log"
done;done
sha256sum "$verifier" "$pool" "$registry" "$svm" > "$out/artifact-hashes.txt"
