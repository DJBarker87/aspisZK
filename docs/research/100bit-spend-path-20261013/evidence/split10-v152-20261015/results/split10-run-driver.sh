#!/usr/bin/env bash
set -euo pipefail
ulimit -c 0
w=/home/dombarker/project-offloads/aspis-r1-split10-run-20261015
src="$w/source"
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=/home/dombarker/project-offloads/aspis-100bit-field-parser-candidate-20261014/cargo-target-v152
export ASPIS_SOURCE_REVISION=aba310f1daa065a27da89d15c6c47166037a8a71+shared-point-68c9087712ff6bfb08c7ed41a1281798466e6671800761c80f83126963262f63+split10-gate-f8986a966a6b17340c84c8d6a3514eed061f25cba8f8d65433d458dc8f379406
cd "$src"
exec /usr/bin/python3 /home/dombarker/project-offloads/aspis-100bit-path-20261013/scripts/v8_state_only_cu_record.py "$w/results/driver-build" /home/dombarker/.cargo/bin/cargo build --release --locked --offline --manifest-path "$src/tools/r1-cost-probe/Cargo.toml" --bin pool_gate --features private-leaf-salts
