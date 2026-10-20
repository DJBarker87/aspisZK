#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-cx-pin-20261020
# Run only after the sequential plan has passed.
test -f "$H/ALL-PASS"
cp -a --reflink=auto /home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/sbf-target-pool "$H/"
mkdir -p "$H/artifacts/pool" "$H/stack/pool"
export CARGO_TARGET_DIR=$H/sbf-target-pool
export CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4'
"$H/harness/capped-run.sh" build-pool "Incremental optimized SBF Pool compilation/link; no arithmetic execution" "$H/src" -- env -u RUSTFLAGS /home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf --manifest-path "$H/src/programs/aspis-pool/Cargo.toml" --sbf-out-dir "$H/artifacts/pool" --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit --skip-tools-install --offline -j 4 -- --locked
cp "$H/sbf-target-pool/sbpf-solana-solana/release/aspis_pool.so" "$H/artifacts/pool/linked.elf"
test "$(sha256sum "$H/artifacts/pool/aspis_pool.so" | cut -d ' ' -f 1)" = 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
cp "$H/artifacts/pool/linked.elf" "$H/stack/pool/linked.elf"
cp "$H/artifacts/pool/aspis_pool.so" "$H/stack/pool/stripped.so"
cat "$H/receipts/build-pool/stdout.log" "$H/receipts/build-pool/stderr.log" > "$H/stack/pool/build.log"
"$H/harness/capped-run.sh" stack-pool "Strict complete linked Pool ELF audit" "$H" -- python3 "$H/harness/strict-stack.py" "$H/stack/pool"
