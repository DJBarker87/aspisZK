#!/usr/bin/env bash
set -euo pipefail
ulimit -c 0
w=/home/dombarker/project-offloads/aspis-r1-split10-run-20261015
src="$w/source"
sol=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin
export PATH="$sol:/home/dombarker/.cargo/bin:/usr/bin:/bin"
export CARGO_TARGET_DIR=/home/dombarker/project-offloads/aspis-100bit-field-parser-candidate-20261014/cargo-target-v152
export ASPIS_SOURCE_REVISION=aba310f1daa065a27da89d15c6c47166037a8a71+shared-point-68c9087712ff6bfb08c7ed41a1281798466e6671800761c80f83126963262f63+split10-294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a-b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4
cd "$src"
exec /usr/bin/python3 /home/dombarker/project-offloads/aspis-100bit-path-20261013/scripts/v8_state_only_cu_record.py "$w/results/sbf-build" "$sol/cargo-build-sbf" --manifest-path "$src/programs/r1-cost-probe/Cargo.toml" --sbf-out-dir "$w/bin-split10" --features pool-adapter,private-leaf-salts -- --locked -j 2
