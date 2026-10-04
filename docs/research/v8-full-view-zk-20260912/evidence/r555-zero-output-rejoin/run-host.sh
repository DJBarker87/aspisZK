#!/usr/bin/env bash
set -euo pipefail
root=/home/dombarker/project-offloads/aspis-r117-zero-output-rejoin-20261004-a
ex="$root/docs/research/v8-no-work-100-20260907/experiments"
evidence="$root/zero-output-rejoin-evidence"
out="$evidence/run-zero-output-seed1"
test ! -e "$out"
SECONDS=0
finish() { status=$?; trap - EXIT; echo "script_exit=$status wall_seconds=$SECONDS"; exit "$status"; }
trap finish EXIT
exec > >(tee "$evidence/run-zero-output-seed1.log") 2>&1
echo "utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "source_revision=6677d5f1310ff7373301fbd79f186278f772e68a"
echo "diagnostic=one fixed seed1; one programmed post-round0 compact squeeze; recipient_zero fixture; no search/retry"
echo "program=full actual R117 selected host verifier and full proof constructor; ordinary corruption/canonical controls retained"
echo "accounting=each selected verifier entrypoint performs both optimized and dense/reference semantic replay"
echo "output=$out"
sha256sum "$evidence/selected-rustflags.txt" \
  "$ex/relation_callback.rs" "$ex/payment_extraction.rs" \
  "$ex/performance.rs" "$ex/semantic_rejoin_oracle.rs" \
  "$ex/performance-host/target/release/aspis-v8-performance-host"
grep -E 'MemAvailable|SwapFree' /proc/meminfo
free -h
systemd-cgls --user --no-pager | rg -n 'aspis-|lean|cargo|rustc' || true
flags="$(cat "$evidence/selected-rustflags.txt") --cfg v8_semantic_rejoin"
unit="aspis-v8-semantic-rejoin-run-$(date +%s)-$$"
echo "unit=$unit MemoryHigh=5G MemoryMax=7G MemorySwapMax=0 TasksMax=128"
printf 'RUSTFLAGS=%s\n' "$flags"
printf 'command=aspis-v8-performance-host %s\n' "$out"
systemd-run --user --wait --collect --pipe --unit="$unit" \
  --working-directory="$ex" \
  -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/time -v env \
    -u ASPIS_V8_LIVE_CONTEXT -u ASPIS_V8_COMPLETE_CONTEXT \
    -u ASPIS_V8_MAX_FRONTIER_SCAN -u ASPIS_R17_C1_WITNESS_AUDIT \
    -u ASPIS_R17_H1_SEMANTIC_AUDIT -u ASPIS_R17_COUPLED_AUDIT \
    NO_DNA=1 ASPIS_V8_POSITIVE_CASE=recipient_zero RUSTFLAGS="$flags" \
    CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true \
    PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin \
    "$ex/performance-host/target/release/aspis-v8-performance-host" "$out"
echo "run_exit=0"
