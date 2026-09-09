#!/usr/bin/env bash
# Run only after authoritative-before-proof.json is exported and authenticated.
set -euo pipefail
umask 077
readonly root=/home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909
readonly demo="$root/docs/research/v8-isolated-devnet-smoke-20260909"
[[ "$PWD" == "$root" && ! -e .git ]]
[[ -f "$root/live-context/statement.bin" && ! -e "$root/live-proof" ]]
[[ -z "${ASPIS_V8_MAX_FRONTIER_SCAN+x}" ]]
# Operator records host reservations immediately before this bounded optimized job.
# Expected work: genuine proof generation; no compilation or transcript search.
systemd-run --user --scope --unit=aspis-v8-live-prover \
  -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v \
  env NO_DNA=1 \
  ASPIS_V8_LIVE_CONTEXT="$root/live-context" \
  ASPIS_V8_COMPLETE_CONTEXT="$root/live-context" \
  "$root/docs/research/v8-no-work-100-20260907/experiments/performance-host/target/release/aspis-v8-performance-host" \
  "$root/live-proof"
