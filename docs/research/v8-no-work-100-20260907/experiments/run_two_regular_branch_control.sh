#!/bin/sh
set -eu
cd "$(dirname "$0")"
task_dir=$(mktemp -d /tmp/aspis-two-regular-branch.XXXXXX)
printf 'RETAINED_BINARY=%s/control\n' "$task_dir"
rustc --edition=2021 -O -C overflow-checks=yes TwoRegularBranchControl.rs -o "$task_dir/control"
"$task_dir/control"
