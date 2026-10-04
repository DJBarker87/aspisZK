#!/usr/bin/env bash
set -euo pipefail
cd /home/dombarker/project-offloads/aspis-r117-g-obstruction-source-certificate-20261004-a
export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
export RUSTFLAGS="$(cat rustflags.txt)"
set +e
/usr/bin/time -v cargo build -vv --offline --locked --release --jobs 1 --manifest-path docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml --bin aspis-v8-performance-host --features insecure-spend-fixture,selected-v7-kernels 2>&1 | tee evidence/r550-g-obstruction-source-certificate/build-attempt2.log
status=${PIPESTATUS[0]}
set -e
printf "%s\n" "$status" > evidence/r550-g-obstruction-source-certificate/build-attempt2.exit
exit "$status"
