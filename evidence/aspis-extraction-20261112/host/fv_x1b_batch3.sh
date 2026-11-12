#!/bin/bash
# X1b batch 3, INSIDE one fv_slot.sh scope: frozen-copy test baselines (both program configurations); tests of the final
# tree rw-G; SBF builds of rw-G and of the F alternative rw-F2 with replays; objdump function comparison of every item
# ELF against the frozen one; the final emission of rw-G with native probe and gates.
set -u
W=/home/dombarker/project-offloads/future-version-20261111; X=$W/x1b; cd $W
echo "== $(date -u +%T) tests"
bash $X/bin/fv_x1b_test.sh rw-0 program program2 > $X/logs/test-0.log 2>&1; grep -E "^STEP|test result" $X/logs/test-0.log
bash $X/bin/fv_x1b_test.sh rw-G program program2 verifier > $X/logs/test-G.log 2>&1; grep -E "^STEP|test result" $X/logs/test-G.log
echo "== $(date -u +%T) builds"
bash $X/bin/fv_x1b_build.sh rw-G G both
bash $X/bin/fv_x1b_build.sh rw-F2 F2 aspis
for n in G F2; do bash $X/bin/fv_x1b_replay.sh $n $W/out/X1b-$n/artifacts/aspis_r1_cost_probe_program.so; done
echo "== $(date -u +%T) objdump"
OD=$(ls -d $HOME/.cache/solana/*/platform-tools/llvm/bin/llvm-objdump 2>/dev/null | tail -1); echo "objdump $OD"
mkdir -p $X/elfdiff
for n in 0 C1 D J F L K G F2; do $OD -d --no-show-raw-insn $W/out/X1b-$n/artifacts/aspis_r1_cost_probe_program.so > $X/elfdiff/$n.txt 2>&1; done
for n in C1 D J F L K G F2; do python3 -I $X/bin/fv_x1b_elfdiff.py $X/elfdiff/0.txt $X/elfdiff/$n.txt > $X/elfdiff/0-vs-$n.tsv; tail -1 $X/elfdiff/0-vs-$n.tsv; done
p=0; for n in C1 D J F L K G; do python3 -I $X/bin/fv_x1b_elfdiff.py $X/elfdiff/$p.txt $X/elfdiff/$n.txt > $X/elfdiff/$p-vs-$n.tsv; echo "$p->$n $(tail -1 $X/elfdiff/$p-vs-$n.tsv)"; p=$n; done
python3 -I $X/bin/fv_x1b_elfdiff.py $X/elfdiff/F.txt $X/elfdiff/F2.txt > $X/elfdiff/F-vs-F2.tsv; tail -1 $X/elfdiff/F-vs-F2.tsv
echo "== $(date -u +%T) emission"; bash $X/bin/fv_x1b_job.sh G $X/bin/fv_x1b_cfg_G.json
echo "== $(date -u +%T) emission done"; mkdir -p $X/gates-out
echo "== $(date -u +%T) gates validation"
(cd $X/probe/crate-m && env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 cargo generate-lockfile --offline > $X/logs/probe-m-lock.log 2>&1)
bash $X/bin/fv_x1b_job.sh probe-m $X/bin/fv_x1b_cfg_probe_m.json noabort
python3 -I $X/bin/fv_x1b_mutiter.py $X/runs/probe-m/runs/C/out.llbc x1b_probe_m > $X/gates-out/mutiter-probe-m.tsv
python3 -I $X/bin/fv_x1b_mutiter.py $X/runs/G/runs/C/out.llbc > $X/gates-out/mutiter-G.tsv
python3 -I $X/gates/mutiter_calls.py $X/runs/G/runs/C/out.llbc $X/gates-out/pv-mutiter-G.json > $X/gates-out/pv-mutiter-G.log 2>&1; echo "pv mutiter exit $?"
python3 -I $X/gates/inventory_text.py $W/x1/runs/off2/runs/A-release/raw/AspisX1 $X/gates-out/pv-inventory-off2.json > $X/gates-out/pv-inventory-off2.log 2>&1; echo "pv inventory off2 exit $?"
python3 -I $X/gates/inventory_text.py $X/runs/G/runs/A-release/raw/AspisX1 $X/gates-out/pv-inventory-G.json > $X/gates-out/pv-inventory-G.log 2>&1; echo "pv inventory G exit $?"
python3 -I $X/gates/p2_bodycmp.py $X/runs/C/runs/A-release/raw/AspisX1/Funs.lean $X/runs/G/runs/A-release/raw/AspisX1/Funs.lean $X/gates-out/pv-bodycmp-C-G.json > $X/gates-out/pv-bodycmp-C-G.log 2>&1; echo "pv bodycmp exit $?"
python3 -I $X/gates/p2_bodycmp.py $X/runs/E/runs/A-release/raw/AspisX1/Funs.lean $X/runs/G/runs/A-release/raw/AspisX1/Funs.lean $X/gates-out/pv-bodycmp-E-G.json > $X/gates-out/pv-bodycmp-E-G.log 2>&1; echo "pv bodycmp E-G exit $?"
python3 -I $X/bin/fv_x1b_targetos.py $X/rw-G $X/runs/G/runs/A-release/raw/AspisX1 > $X/gates-out/target-os.tsv
echo "== $(date -u +%T) all done"
