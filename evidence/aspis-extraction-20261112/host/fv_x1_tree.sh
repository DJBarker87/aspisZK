#!/bin/bash
# X1: resolved feature sets of the deployed build (programs/r1-cost-probe, --features aspis) on the frozen tree.
# Runs INSIDE one fv_slot.sh scope. Reads only the source tree; writes only under W/x1/tree.
# Two resolutions: the host target (what Charon compiles for) and the SBF target with the platform tools'
# cargo that cargo-build-sbf 3.1.13 uses (what the deployed ELF is built for).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
S=$W/src-frz-a; O=$W/x1/${X1_TREE_OUT:-tree}; mkdir -p $O
M=$S/programs/r1-cost-probe/Cargo.toml
cd $S
for P in aspis-r1-cost-probe-program aspis-r1-cost-probe aspis-statement aspis-core; do
  env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$W/x1/target/tree CARGO_NET_OFFLINE=true \
    cargo tree --manifest-path $M --locked --offline --features aspis -e features -i $P > $O/host-inv-$P.txt 2>&1; echo "host $P $?" >> $O/exit.txt
done
env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$W/x1/target/tree CARGO_NET_OFFLINE=true \
  cargo tree --manifest-path $M --locked --offline --features aspis -e features > $O/host-full.txt 2>&1; echo "host full $?" >> $O/exit.txt
PT=$(ls -d /home/dombarker/.cache/solana/v1.5*/platform-tools/rust/bin | tail -1)
echo "platform tools $PT" >> $O/exit.txt
for P in aspis-r1-cost-probe-program aspis-r1-cost-probe aspis-statement aspis-core; do
  env PATH=$PT:/usr/bin:/bin CARGO_TARGET_DIR=$W/x1/target/tree-sbf CARGO_NET_OFFLINE=true \
    $PT/cargo tree --manifest-path $M --locked --offline --features aspis --target sbpf-solana-solana -e features -i $P > $O/sbf-inv-$P.txt 2>&1; echo "sbf $P $?" >> $O/exit.txt
done
# one line per package: name version | enabled features (the summary the README quotes)
env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$W/x1/target/tree CARGO_NET_OFFLINE=true \
  cargo tree --manifest-path $M --locked --offline --features aspis -e normal --prefix none -f '{p}|{f}' > $O/host-pkgfeatures.txt 2>&1; echo "host pkgfeatures $?" >> $O/exit.txt
env PATH=$PT:/usr/bin:/bin CARGO_TARGET_DIR=$W/x1/target/tree-sbf CARGO_NET_OFFLINE=true \
  $PT/cargo tree --manifest-path $M --locked --offline --features aspis --target sbpf-solana-solana -e normal --prefix none -f '{p}|{f}' > $O/sbf-pkgfeatures.txt 2>&1; echo "sbf pkgfeatures $?" >> $O/exit.txt
exit 0
