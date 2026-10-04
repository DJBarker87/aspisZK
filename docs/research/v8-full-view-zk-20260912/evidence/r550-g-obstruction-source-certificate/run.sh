#!/usr/bin/env bash
set -euo pipefail
root=/home/dombarker/project-offloads/aspis-r117-g-obstruction-source-certificate-20261004-a
cd "$root"
exec /usr/bin/time -v "$root/docs/research/v8-no-work-100-20260907/experiments/performance-host/target/release/aspis-v8-performance-host" --g-obstruction-existing "$root/evidence/r550-g-obstruction-source-certificate" "$root/evidence/r550-g-obstruction-source-certificate/export"
