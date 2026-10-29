#!/bin/sh
# Reviewed Linux client recipe; root-workspace SBF builds never invoke this.
set -eu
cd "$(dirname "$0")"
unset CARGO_ENCODED_RUSTFLAGS CARGO_PROFILE_CLIENT_PANIC RUSTC_BOOTSTRAP
export RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4'
exec cargo build --profile client --locked --offline -j 4 \
  --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend
