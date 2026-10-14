#!/usr/bin/env bash
set -u

ROOT=/home/dombarker/project-offloads/aspis-r1-parser-limbs-20261014
EVIDENCE="$ROOT/evidence"
UNIT=aspis-r1-parser-limbs-20261014
mkdir -p "$EVIDENCE"
START_UTC="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
set +e
systemd-run --user --scope --quiet --unit="$UNIT" \
  -p MemoryHigh=4G -p MemoryMax=6G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/bash "$EVIDENCE/job-inner.sh" > "$EVIDENCE/systemd-run.log" 2>&1
STATUS=$?
set -e
END_UTC="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
printf 'start_utc=%s\nend_utc=%s\nexit_status=%s\nunit=%s.scope\nMemoryHigh=4G\nMemoryMax=6G\nMemorySwapMax=0\nTasksMax=128\n' \
  "$START_UTC" "$END_UTC" "$STATUS" "$UNIT" > "$EVIDENCE/run-receipt.txt"
exit "$STATUS"
