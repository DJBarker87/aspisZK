#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$1"
[[ "$(sha256sum "$ex/joined_inverse.rs" | cut -d' ' -f1)" == 4913337c4f5467db15ce58e680b7252e099fb597c2ef303edfe94165b2a9ba05 &&
   "$(sha256sum "$ex/circle_norm.rs" | cut -d' ' -f1)" == 46fa71b10b99950d5ab4b718964007d3b290b26ac51491e0e35a51d225178f2d &&
   "$(sha256sum "$ex/relation_callback.rs" | cut -d' ' -f1)" == facf34d9636e2092c6b707aa9785f1dce1fbd6d0518eb180bfba26c9d66cbf18 ]] || exit 2
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
cd "$rt"
# Compilation dominates; new inversion-fusion tests only, optimized and capped.
systemd-run --user --scope --unit="aspis-joined-inverse-test-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env RUSTFLAGS='--cfg v8_joined_inverse --cfg v8_circle_norm --cfg v8_chord_norm --cfg v8_batch_m --cfg v8_leaf_record --cfg v8_merkle_slices --cfg v8_merkle_borrow -C overflow-checks=yes -A dead_code -A unexpected_cfgs' cargo test --offline --locked --release --jobs 2 --manifest-path "$ex/performance-host/Cargo.toml" joined_inverse::tests -- --test-threads=1 --nocapture 2>&1 | tee "$log"
sha256sum "$ex/relation_callback.rs" "$ex/circle_norm.rs" "$ex/joined_inverse.rs" >> "$log"
