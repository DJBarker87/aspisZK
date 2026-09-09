#!/usr/bin/env bash
set -euo pipefail
umask 077
readonly root=/home/dombarker/project-offloads/aspis-v8-positive-complete-20260909
readonly d="$root/docs/research/v8-positive-complete-devnet-20260909" ex="$root/docs/research/v8-no-work-100-20260907/experiments"
cd "$root"
[[ -f "$root/positive-live-context/statement.bin" && -z "${ASPIS_V8_MAX_FRONTIER_SCAN+x}" ]]
for c in honest recipient_zero change_zero; do
 [[ ! -e "$root/positive-live-$c" ]]
 systemd-run --user --scope --unit="aspis-positive-live-$c-$(date +%s)" \
  -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v \
  env NO_DNA=1 ASPIS_V8_POSITIVE_CASE="$c" \
  ASPIS_V8_LIVE_CONTEXT="$root/positive-live-context" ASPIS_V8_COMPLETE_CONTEXT="$root/positive-live-context" \
  "$ex/performance-host/target/release/aspis-v8-performance-host" "$root/positive-live-$c" \
  > "$d/evidence/live-prover-$c.log" 2>&1
 "$root/demo-host-target/release/aspis-v8-devnet-tools" case-terminal "$d/identities.json" "$root/positive-live-$c" \
  > "$d/evidence/live-case-$c-binding.log" 2>&1
done
