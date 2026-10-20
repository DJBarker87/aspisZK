#!/usr/bin/env bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021
export CARGO_TARGET_DIR=$H/sbf-target-pool
export CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4'
mkdir -p "$H/artifacts/pool"
python3 "$H/harness/reservation.py" "$H/reservation-pool-build.json" >/dev/null
"$H/harness/capped-run.sh" pool-build-v1 'Incremental optimized SBF Pool compilation/link; verify gated references leave frozen ELF unchanged' "$H/src" -- env -u RUSTFLAGS /home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf --manifest-path "$H/src/programs/aspis-pool/Cargo.toml" --sbf-out-dir "$H/artifacts/pool" --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit --skip-tools-install --offline -j 4 -- --locked
sha256sum "$H/artifacts/pool/aspis_pool.so" > "$H/pool-elf.sha256"
stat -c '%s bytes' "$H/artifacts/pool/aspis_pool.so" > "$H/pool-elf.size"
