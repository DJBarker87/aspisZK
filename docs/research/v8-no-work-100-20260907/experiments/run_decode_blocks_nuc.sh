#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$1"
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
cd "$rt"
# Compilation dominates; arbitrary-byte decoder and gamma tests are small.
systemd-run --user --scope --unit="aspis-decode-blocks-test-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env RUSTFLAGS='--cfg v8_gamma_wrap --cfg v8_gamma_fixed --cfg v8_decode_blocks --cfg v8_gamma_partial --cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_qm_channel_partial --cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook -C overflow-checks=yes -A dead_code -A unexpected_cfgs' cargo test --offline --locked --release --jobs 2 --manifest-path "$ex/performance-host/Cargo.toml" query_arithmetic::decode_tests -- --test-threads=1 --nocapture 2>&1 | tee "$log"
sha256sum "$ex/query_arithmetic.rs" >> "$log"
