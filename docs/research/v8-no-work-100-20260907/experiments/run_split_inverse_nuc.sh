#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$1"
[[ "$(sha256sum "$ex/joined_inverse.rs" | cut -d' ' -f1)" == f35b817eada8abe71a0b44d754c55cd6dfb0603c919ee3d937a8059371bb7b74 &&
   "$(sha256sum "$ex/circle_norm.rs" | cut -d' ' -f1)" == 6412dfd36176df2523421238b655e8a0fa1a5d6fa0c9196e461604ebf181e726 &&
   "$(sha256sum "$ex/relation_callback.rs" | cut -d' ' -f1)" == 4ba7201b917ab21340fd6cbc2d3af231169f7c5c85934e2a79584aa3e89a4512 ]] || exit 2
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
cd "$rt"
# Compilation dominates; new inversion-fusion tests only, optimized and capped.
systemd-run --user --scope --unit="aspis-split-inverse-test-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env RUSTFLAGS='--cfg v8_split_inverse --cfg v8_joined_inverse --cfg v8_circle_norm --cfg v8_chord_norm --cfg v8_batch_m --cfg v8_leaf_record --cfg v8_merkle_slices --cfg v8_merkle_borrow -C overflow-checks=yes -A dead_code -A unexpected_cfgs' cargo test --offline --locked --release --jobs 2 --manifest-path "$ex/performance-host/Cargo.toml" joined_inverse::tests -- --test-threads=1 --nocapture 2>&1 | tee "$log"
sha256sum "$ex/relation_callback.rs" "$ex/circle_norm.rs" "$ex/joined_inverse.rs" >> "$log"
