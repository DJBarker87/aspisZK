#!/usr/bin/env bash
set -euo pipefail
# Run in a task-owned bounded zero-swap Linux scope. Optimized, dependency-free.
source_dir=${1:?pinned source directory}
task=${2:?fresh output directory}
kit=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
test ! -e "$task"
test "$(sha256sum "$source_dir/field.rs" | cut -d' ' -f1)" = 5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8
test "$(sha256sum "$source_dir/r17_structured_g.rs" | cut -d' ' -f1)" = 147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6
mkdir -p "$task"
cp "$source_dir/field.rs" "$source_dir/r17_structured_g.rs" "$kit/allocation_probe.rs" "$task/"
rustc=/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc
"$rustc" --version
/usr/bin/time -v "$rustc" --edition=2021 -O "$task/allocation_probe.rs" -o "$task/allocation-probe"
sha256sum "$task/allocation-probe"
/usr/bin/time -v python3 "$kit/check_allocation.py" "$task/allocation-probe" > "$task/results.json"
