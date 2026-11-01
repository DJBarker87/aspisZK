#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-pv-c474-20261029
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_TARGET_DIR="$H/native-target"
unset CARGO_ENCODED_RUSTFLAGS RUSTC_BOOTSTRAP
export RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4'
cd "$H/src/tools/pv-c474-validation"
cargo build --profile client --locked --offline -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin pv-c474-differential --bin pv-c474-fixture
# Graph-only query, no compiler/code generation under bootstrap.
RUSTC_BOOTSTRAP=1 cargo build --profile client --locked --offline -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin pv-c474-differential --bin pv-c474-fixture -Z unstable-options --unit-graph > "$H/client-harness-unit-graph.json"
