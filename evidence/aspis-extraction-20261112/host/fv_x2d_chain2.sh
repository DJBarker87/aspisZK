#!/bin/bash
# X2d chain 2 (nohup), one fv_slot.sh scope at a time:
#   tests and recorder dumps of the item 1 tree; dump comparison against X2c's frozen dumps (W/x2c/dump-frz-c5, read
#   only: the frozen tree is unchanged since that run); the single-root emission and native compile; the light
#   checks (X2c's emission checks, the read-after-write check, the grammar checker); the SBF build of the item 1 tree
#   (copied to W/src-x2d-<suffix>); the compute replays of the item 1 Pool.
# Usage: fv_x2d_chain2.sh <suffix>   (a new suffix per launch; attempt names X2d-<step>-<suffix>)
set -u
N=$1
W=/home/dombarker/project-offloads/future-version-20261111
X=$W/x2d; S=$X/st; R=$X/rw-tree
cd $W
bash $X/bin/fv_x2d_job.sh test-$N 3000 $S bash $X/bin/fv_x2d_test.sh $R test $X/dump-rw-$N
if [ "$(cat $S/status-test-$N)" != 0 ]; then echo "tests failed" > $S/chain2-$N.done; exit 1; fi
python3 -I $X/bin/fv_x2c_compare_dumps.py $W/x2c/dump-frz-c5 $X/dump-rw-$N > $X/compare-$N.txt 2>&1; echo "compare exit $?" >> $X/compare-$N.txt
bash $X/bin/fv_x2d_job.sh pool-$N 3000 $S bash $X/bin/fv_x2d_emit.sh $X/bin/fv_x2d_cfg_1.json $X/pool-$N charon,aeneas,scan native
RAW=$X/pool-$N/runs/A-release/raw/AspisX2
P=$R/programs/aspis-pool/src
python3 -I $X/bin/fv_x2c_emission_checks.py $RAW account_write.write_account_data_v1 solana_account_info.AccountInfo.try_borrow_data $P,$R/crates/aspis-statement/src,$R/crates/aspis-core/src $P/account_write.rs > $X/emission-checks-$N.txt 2>&1; echo "exit $?" >> $X/emission-checks-$N.txt
READS=solana_account_info.AccountInfo.try_borrow_data,solana_account_info.AccountInfo.data_len,solana_account_info.AccountInfo.data_is_empty,solana_account_info.AccountInfo.impl.lamports
ROOTS=pair_forest.process_pair_forest_initialize_with_runtime_v1,pair_forest.process_pair_forest_checkpoint_with_runtime_v1,pair_forest.process_pair_forest_deposit_with_runtime_v1,pair_forest.process_pair_forest_terminal_v1,processor.process_instruction
python3 -I $X/bin/fv_emit_read_after_write.py --funs $RAW/Funs.lean --write account_write.write_account_data_v1 --read $READS --root $ROOTS --list-reached > $X/read-after-write-$N.txt 2>&1; echo "exit $?" >> $X/read-after-write-$N.txt
python3 -I $X/bin/fv_x2c_write_boundary_check.py $P/account_write.rs > $X/grammar-$N.txt 2>&1; echo "exit $?" >> $X/grammar-$N.txt
test -e $W/src-x2d-$N || cp -a $R $W/src-x2d-$N
bash $X/bin/fv_x2d_job.sh build-x2d-$N 3000 $S bash $X/bin/fv_x2d_pool_build.sh X2d-build-x2d-$N src-x2d-$N
bash $X/bin/fv_x2d_job.sh compute-x2d-$N 900 $S bash $X/bin/fv_x2d_compute.sh $X/compute-x2d-$N x2d=$X/out/X2d-build-x2d-$N/artifacts/aspis_pool.so
echo done > $S/chain2-$N.done
