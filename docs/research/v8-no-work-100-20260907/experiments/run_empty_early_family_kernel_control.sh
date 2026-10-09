#!/bin/bash
set -euo pipefail
# Tiny local macOS control, explicitly authorized by root. No Cargo/dependencies.
# CPU/file/descriptor limits are safety guards, not a Linux cgroup/swap claim.
ulimit -t 60
ulimit -f 131072
ulimit -n 128
control_dir=$(cd "$(dirname "$0")" && pwd)
control_tmp=$(mktemp -d "${TMPDIR:-/tmp}/empty-early-family.XXXXXXXX")
control_source="$control_dir/EmptyEarlyFamilyKernelControl.rs"
control_binary="$control_tmp/empty-early-family-kernel-control"
printf 'SOURCE_REVISION=%s\n' "$(git -C "$control_dir" rev-parse HEAD)"
printf 'PLATFORM=%s\n' "$(uname -srm)"
printf 'BINARY_TEMP_PATH=%s\n' "$control_binary"
rustc --version
shasum -a 256 "$control_source" "$0"
printf 'COMPILE_COMMAND=rustc --edition=2021 -O -C overflow-checks=yes SOURCE -o BINARY\n'
/usr/bin/time -l rustc --edition=2021 -O -C overflow-checks=yes "$control_source" -o "$control_binary"
printf 'COMPILE_EXIT=0\n'
shasum -a 256 "$control_binary"
/usr/bin/time -l "$control_binary"
printf 'CONTROL_EXIT=0\n'
