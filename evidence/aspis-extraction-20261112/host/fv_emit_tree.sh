#!/bin/bash
# X7: resolved feature sets of both deployed builds of one source tree, host target (what Charon compiles for,
# nightly-2026-09-17) and SBF target (sbpf-solana-solana, the platform tools' cargo that cargo-build-sbf 3.1.13 uses):
# the method of X1's fv_x1_tree.sh and X2's fv_x2_tree.sh. Reads only the tree. Runs INSIDE the fv_slot.sh scope of
# fv_emit_job.sh. Usage: fv_emit_tree.sh <tree dir> <out dir> <cargo target dir>
# Output per program P (verifier, pool): P-host-features.txt, P-sbf-features.txt (cargo tree -e features, full),
# P-host-pkgfeatures.txt, P-sbf-pkgfeatures.txt ('{p}|{f}' per package), exit.txt.
set -u
S=$1; O=$2; T=$3; mkdir -p $O
PT=$(ls -d /home/dombarker/.cache/solana/v1.5*/platform-tools/rust/bin | tail -1)
echo "platform tools $PT" > $O/exit.txt
H="env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$T/tree CARGO_NET_OFFLINE=true cargo"
SB="env PATH=$PT:/usr/bin:/bin CARGO_TARGET_DIR=$T/tree-sbf CARGO_NET_OFFLINE=true $PT/cargo"
cd $S
for P in verifier pool; do
  if [ $P = verifier ]; then M=$S/programs/r1-cost-probe/Cargo.toml; FE=aspis; else M=$S/programs/aspis-pool/Cargo.toml; FE=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit; fi
  $H tree --manifest-path $M --locked --offline --features $FE -e features > $O/$P-host-features.txt 2>&1; echo "$P host features $?" >> $O/exit.txt
  $SB tree --manifest-path $M --locked --offline --features $FE --target sbpf-solana-solana -e features > $O/$P-sbf-features.txt 2>&1; echo "$P sbf features $?" >> $O/exit.txt
  $H tree --manifest-path $M --locked --offline --features $FE -e normal --prefix none -f '{p}|{f}' > $O/$P-host-pkgfeatures.txt 2>&1; echo "$P host pkgfeatures $?" >> $O/exit.txt
  $SB tree --manifest-path $M --locked --offline --features $FE --target sbpf-solana-solana -e normal --prefix none -f '{p}|{f}' > $O/$P-sbf-pkgfeatures.txt 2>&1; echo "$P sbf pkgfeatures $?" >> $O/exit.txt
done
grep -n -A3 '^\[profile' $S/Cargo.toml $S/programs/r1-cost-probe/Cargo.toml $S/programs/aspis-pool/Cargo.toml > $O/profiles.txt 2>&1
ls -a $S/.cargo 2>/dev/null > $O/dot-cargo.txt; cat $S/.cargo/config.toml >> $O/dot-cargo.txt 2>/dev/null
! grep -q ' [1-9][0-9]*$' <(grep -v 'platform tools' $O/exit.txt)
