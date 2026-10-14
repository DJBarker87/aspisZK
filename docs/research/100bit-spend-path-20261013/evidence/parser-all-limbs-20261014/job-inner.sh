#!/usr/bin/env bash
set -u

ROOT=/home/dombarker/project-offloads/aspis-r1-parser-limbs-20261014
EVIDENCE="$ROOT/evidence"
mkdir -p "$EVIDENCE"
cd "$ROOT"
export PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin
export CARGO_HOME=/home/dombarker/.cargo
export CARGO_TARGET_DIR=/home/dombarker/project-offloads/aspis-r1-p2-20261010/target
export CARGO_BUILD_JOBS=2

printf 'source_root=%s\n' "$ROOT" > "$EVIDENCE/environment.txt"
printf 'cargo_target_dir=%s\n' "$CARGO_TARGET_DIR" >> "$EVIDENCE/environment.txt"
printf 'cargo_version=%s\n' "$(cargo --version)" >> "$EVIDENCE/environment.txt"
printf 'rustc_version=%s\n' "$(rustc --version)" >> "$EVIDENCE/environment.txt"
printf 'rustc_host=%s\n' "$(rustc -vV | sed -n 's/^host: //p')" >> "$EVIDENCE/environment.txt"
printf 'uname=%s\n' "$(uname -a)" >> "$EVIDENCE/environment.txt"

set +e
/usr/bin/time -v -o "$EVIDENCE/time.log" cargo test --release --locked -p aspis-r1-cost-probe --test validated_prefix semantic_rows_reject_noncanonical_limbs_at_every_wide_position > "$EVIDENCE/out.log" 2>&1
STATUS=$?
set -e

CGROUP_REL="$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)"
CGROUP_DIR="/sys/fs/cgroup${CGROUP_REL}"
printf 'exit_status=%s\n' "$STATUS" > "$EVIDENCE/exit-status.txt"
printf 'cgroup=%s\n' "$CGROUP_DIR" > "$EVIDENCE/cgroup.txt"
cat "$CGROUP_DIR/memory.peak" > "$EVIDENCE/cgroup-memory-peak-bytes.txt"
cat "$CGROUP_DIR/memory.swap.current" > "$EVIDENCE/cgroup-swap-current-bytes.txt"
cat "$CGROUP_DIR/memory.events" > "$EVIDENCE/cgroup-memory-events.txt"
exit "$STATUS"
