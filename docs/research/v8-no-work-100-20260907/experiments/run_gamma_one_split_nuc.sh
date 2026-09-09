#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$1"
[[ "$(sha256sum "$ex/query_arithmetic.rs" | cut -d' ' -f1)" == e76be758a94a4350050122f2cb822d58cd5d9f2746deebb5b881d8327570bd41 && "$(sha256sum "$ex/relation_callback.rs" | cut -d' ' -f1)" == b34acafe1b7735915d2e250725f157ee9424b9208cc179470a3c67cd8d13f3db ]] || { echo 'Apply archived gamma-one-split-query.patch and gamma-one-callback.patch to e6373fdc first.' >&2; exit 2; }
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
cd "$rt"
# Compilation dominates; guarded first-chunk and arbitrary-table tests are small.
systemd-run --user --scope --unit="aspis-gamma-one-split-test-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env RUSTFLAGS='--cfg v8_gamma_wrap --cfg v8_gamma_fixed --cfg v8_gamma_one --cfg v8_gamma_one_split --cfg v8_decode_blocks --cfg v8_gamma_partial --cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_qm_channel_partial --cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook -C overflow-checks=yes -A dead_code -A unexpected_cfgs' cargo test --offline --locked --release --jobs 2 --manifest-path "$ex/performance-host/Cargo.toml" query_arithmetic::one_tests -- --test-threads=1 --nocapture 2>&1 | tee "$log"
sha256sum "$ex/query_arithmetic.rs" >> "$log"
