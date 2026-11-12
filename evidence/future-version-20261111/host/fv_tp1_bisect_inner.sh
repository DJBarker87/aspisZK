#!/bin/bash
# Runs INSIDE one fv_slot.sh scope (started by fv_tp1_bisect.sh). See that file.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
TAG=$1; shift
S=src-tp1-var; R=$W/tp1/bisect-$TAG.txt; : > $R
K=pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
mkdir -p replays-v5 tp1/bisect-$TAG
# optional construct probe in the same scope: MINI=<name> runs the second tool pair on tp1/mini/<name> first
if [ -n "${MINI:-}" ]; then
  B2=/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin
  M=$W/tp1/mini/$MINI; O=$W/tp1/runs/TP-M-$TAG-$MINI; mkdir -p $O
  ( cd $M && env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$W/tp1/target/mini-$MINI CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 $B2/charon cargo --preset aeneas --mir built --sysroot default --include core::option::Option --include core::result::Result --dest-file $O/out.llbc -- --offline --release --lib > $O/charon.log 2>&1; echo "charon exit $?" > $O/exits )
  ( cd $O && $B2/aeneas -diagnose-translation -sequential -no-progress-bar -backend lean -namespace Mini -dest $O/raw -subdir Mini -split-files $O/out.llbc > $O/aeneas.log 2>&1; echo "aeneas exit $?" >> $O/exits )
  echo "probe $MINI: $(tr '\n' ';' < $O/exits) rejected: $(sed 's/\x1b\[[0-9;]*m//g' $O/aeneas.log | grep -c 'Could not translate the body')" >> $R
  sed 's/\x1b\[[0-9;]*m//g' $O/aeneas.log | grep -E '^\[Error\]|Could not translate the body|^Source:' | cut -c1-200 >> $R
fi
for V in "$@"; do
  A=tp1-var-$TAG-$V
  cp -R tp1/var-$TAG/B/. $S/ && { [ $V = B ] || cp -R tp1/var-$TAG/$V/. $S/; } || { echo "$V: files missing" >> $R; continue; }
  t0=$(date +%s)
  bash $W/fv_build_adapter_src.sh $A $K $S > tp1/bisect-$TAG/build-$V.log 2>&1 || { echo "$V: BUILD FAILED ($(grep -m1 '^error' tp1/bisect-$TAG/build-$V.log | cut -c1-160))" >> $R; continue; }
  E=$W/out/$A/artifacts/aspis_r1_cost_probe_program.so
  cp $W/target/sbf-adapter-$S/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so tp1/bisect-$TAG/unstripped-$V.so 2>/dev/null
  line="$V: elf $(sha256sum $E | cut -c1-16) $(stat -c %s $E) bytes;"
  for op in transfer withdrawal; do
    ASPIS_SOURCE_REVISION=$(cat $W/SOURCE_REVISION)+$S-$V $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/devnet/verifier-pin2.so $E $op $W/replays-v5/$A-$op.json > tp1/bisect-$TAG/replay-$V-$op.log 2>&1
    cu=$(python3 -c "import json,sys; s=json.load(open('$W/replays-v5/$A-$op.json'))['summary']; ok=s['one_tx_final_state_equals_control'] and s['changed_certificate_rejected'] and s['pinned_format_buffer_rejected']; print(s['one_tx_transaction_cu'], 'ok' if ok else 'CONDITIONS-FAIL')" 2>/dev/null || echo "replay-failed")
    line="$line $op $cu;"
  done
  echo "$line build+replay $(( $(date +%s) - t0 )) s; source $(cut -c1-16 $W/out/$A/source_tree.sha256)" >> $R
done
cp -R tp1/var-$TAG/B/. $S/
echo DONE >> $R
