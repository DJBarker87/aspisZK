#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly out="$1" verifier="$rt/sbf-complete-decode-profile/aspis_v8_complete_sbf.so"
readonly pool="$rt/sbf-pool-zero-fast/aspis_pool.so" registry="$rt/sbf-selected-registry/aspis_registry.so"
readonly double="$rt/sbf-complete/aspis_pair_forest_result_double.so"
readonly svm="$ex/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection"
readonly proof="$rt/complete-max-withdrawal-255-v1/proofs/proof-2.bin"
mkdir "$out"
systemd-run --user --scope --unit="aspis-decode-profile-$(date +%s)-$$" -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v env NO_DNA=1 ASPIS_MATCHED_V7=0 ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 ASPIS_TOKEN_ELF_DIR=/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/litesvm-0.16.0/src/programs/elf "$svm" "$pool" "$verifier" "$registry" "$double" "$out/withdrawal-255-2.json" "$proof" success 1400000 asq8 255 withdrawal 2>&1 | tee "$out/withdrawal-255-2.log"
sha256sum "$verifier" "$pool" "$registry" "$svm" "$ex/query_arithmetic.rs" > "$out/artifact-hashes.txt"
