#!/bin/bash
# Aspis translatability pass: a construct probe. Runs the second tool pair on a small stand-alone crate
# (tp1/mini/<name>, no dependencies) and lists what Aeneas rejects, so that the construct behind a tool error in a
# large function is found without a full run. One fv_slot.sh scope. Not Aspis code and not evidence about Aspis.
# Usage: fv_tp1_mini.sh <name> <attempt>
W=/home/dombarker/project-offloads/future-version-20261111
B=/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin
M=$W/tp1/mini/$1; O=$W/tp1/runs/$2
test -d $M || exit 1; mkdir -p $O || exit 1
bash $W/fv_slot.sh $2 600 bash -c "cd $M && env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$W/tp1/target/mini-$1 CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 $B/charon cargo --preset aeneas --mir built --sysroot default --include core::option::Option --include core::result::Result --dest-file $O/out.llbc -- --offline --release --lib > $O/charon.log 2>&1; echo charon exit \$? > $O/exits; cd $O && $B/aeneas -diagnose-translation -sequential -no-progress-bar -backend lean -namespace Mini -dest $O/raw -subdir Mini -split-files $O/out.llbc > $O/aeneas.log 2>&1; echo aeneas exit \$? >> $O/exits"
cat $O/exits; grep -B2 -A12 -E "^\[Error\]|Error\]" $O/aeneas.log | cut -c1-300 | head -120; ls $O/raw/Mini 2>/dev/null
