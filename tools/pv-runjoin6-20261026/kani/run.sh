#!/bin/sh
set -u
cd /home/dombarker/project-offloads/codex-pv-runjoin-20261026/factory-kani
export PATH="$HOME/.cargo/bin:$PATH"
export CARGO_BUILD_JOBS=4
export CARGO_PROFILE_DEV_OPT_LEVEL=3
mkdir -p pv6-evidence
sha256sum lib.rs selected.rs Cargo.toml Cargo.lock > pv6-evidence/input.sha256
rustc -Vv > pv6-evidence/rustc.txt
cargo kani --version > pv6-evidence/kani-version.txt
n=0
for harness in zeroizing_zero32_source zeroizing_zero64_source split64_values_source split64_halves_independent split64_nonzero_gate_source split64_guard_rejects_zero_field split64_guard_rejects_zero_salt zeroizing_slice_back32 zeroizing_lower_slice_back64 zeroizing_upper_slice_back64 native_factory_preserves_nonce
do
 n=$((n+1))
 printf '%s\tpv6::%s\n' "$n" "$harness" >> pv6-evidence/invocations.tsv
 /usr/bin/time -v -o "pv6-evidence/kani-$n.time" timeout 180 cargo kani --lib -j 4 --output-format terse --harness "pv6::$harness" --exact --verbose > "pv6-evidence/kani-$n.log" 2>&1
 result=$?
 printf '%s\t%s\n' "$n" "$result" >> pv6-evidence/exits.tsv
 printf 'completed %s exit %s\n' "$harness" "$result"
done
