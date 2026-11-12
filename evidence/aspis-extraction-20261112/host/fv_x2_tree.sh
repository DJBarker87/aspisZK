#!/bin/bash
# X2: resolved feature sets of the deployed Pool build (programs/aspis-pool, the PL-frz-a feature list) on the frozen
# tree. Runs INSIDE one fv_slot.sh scope. Reads only the source tree; writes only under W/x2/tree.
# Two resolutions: the host target (what Charon compiles for) and the SBF target with the platform tools' cargo that
# cargo-build-sbf 3.1.13 uses (what the deployed ELF is built for). Same method as fv_x1_tree.sh.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
S=$W/src-frz-a; O=$W/x2/tree; mkdir -p $O
M=$S/programs/aspis-pool/Cargo.toml
FE=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit
cd $S
H="env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$W/x2/target/tree CARGO_NET_OFFLINE=true cargo"
PT=$(ls -d /home/dombarker/.cache/solana/v1.5*/platform-tools/rust/bin | tail -1)
echo "platform tools $PT" > $O/exit.txt
SB="env PATH=$PT:/usr/bin:/bin CARGO_TARGET_DIR=$W/x2/target/tree-sbf CARGO_NET_OFFLINE=true $PT/cargo"
for P in aspis-pool aspis-statement aspis-core; do
  $H tree --manifest-path $M --locked --offline --features $FE -e features -i $P > $O/host-inv-$P.txt 2>&1; echo "host $P $?" >> $O/exit.txt
  $SB tree --manifest-path $M --locked --offline --features $FE --target sbpf-solana-solana -e features -i $P > $O/sbf-inv-$P.txt 2>&1; echo "sbf $P $?" >> $O/exit.txt
done
$H tree --manifest-path $M --locked --offline --features $FE -e features > $O/host-full.txt 2>&1; echo "host full $?" >> $O/exit.txt
$H tree --manifest-path $M --locked --offline --features $FE -e normal --prefix none -f '{p}|{f}' > $O/host-pkgfeatures.txt 2>&1; echo "host pkgfeatures $?" >> $O/exit.txt
$SB tree --manifest-path $M --locked --offline --features $FE --target sbpf-solana-solana -e normal --prefix none -f '{p}|{f}' > $O/sbf-pkgfeatures.txt 2>&1; echo "sbf pkgfeatures $?" >> $O/exit.txt
# the profile settings that apply: any [profile] table in the workspace manifest and in the program manifest
grep -n -A3 '^\[profile' $S/Cargo.toml $M > $O/profiles.txt 2>&1; echo "profiles grep $?" >> $O/exit.txt
exit 0
