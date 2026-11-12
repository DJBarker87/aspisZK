#!/bin/bash
# X7 gate (viii): branch- and call-following read-after-write check (X2d's fv_emit_read_after_write.py, unchanged)
# over the emitted Lean. First on X2d's planted cases (copies in fv_emit_raw_planted/, from
# pool/followup/read-after-write/planted): every positive root (P1-P6) must be reported, every negative root (N1-N3)
# must pass. Then on each program's raw Funs.lean with the config's roots (Pool: the four handlers and
# process_instruction; verifier program: close_checkpoint), write boundaries and read externals. Reads only.
# Usage: fv_emit_gate_raw.sh <run dir> <program config.json>...
set -u
B=$(cd $(dirname $0) && pwd); O=$1; shift
P=$B/fv_emit_raw_planted
RD=solana_account_info.AccountInfo.try_borrow_data,solana_account_info.AccountInfo.data_len,solana_account_info.AccountInfo.data_is_empty,solana_account_info.AccountInfo.impl.lamports
bad=0
echo "== planted positive (each of the six roots must be reported)"
python3 -I $B/fv_emit_read_after_write.py --funs $P/positive/Funs.lean --write account_write.write_account_data_v1 --read $RD \
  --root test.p1_write_then_read,test.p2_write_then_call_reader,test.p3_write_on_one_branch_then_read,test.p4_loop,test.p5_write_then_trait_method,test.p6_match_arm_write_then_read > $O/gates/viii-planted-positive.txt 2>&1
n=$(grep -c '^== root .*: FAIL' $O/gates/viii-planted-positive.txt); echo "roots reported: $n of 6"; [ "$n" = 6 ] || bad=1
echo "== planted negative (each of the three roots must pass)"
python3 -I $B/fv_emit_read_after_write.py --funs $P/negative/Funs.lean --write account_write.write_account_data_v1 --read $RD \
  --root test.n1_dispatch,test.n2_instance_argument,test.n3_match_arms > $O/gates/viii-planted-negative.txt 2>&1; rc=$?
n=$(grep -c '^== root .*: PASS' $O/gates/viii-planted-negative.txt); echo "roots passing: $n of 3 (exit $rc)"; [ "$n" = 3 ] && [ $rc = 0 ] || bad=1
for CF in "$@"; do
  read PR NS W R RT < <(python3 -c "import json,sys;c=json.load(open(sys.argv[1]));print(c['program'],c['ns'],','.join(c['write_boundaries']),','.join(c['raw_reads']),','.join(c['raw_roots']))" $CF)
  python3 -I $B/fv_emit_read_after_write.py --funs $O/$PR/aeneas/raw/$NS/Funs.lean --write $W --read $R --root $RT > $O/gates/viii-$PR.txt 2>&1; rc=$?
  echo "== $PR (exit $rc)"; grep '^== root\|^overall' $O/gates/viii-$PR.txt
  [ $rc = 0 ] || bad=1
done
echo "gate (viii) read after write, branch- and call-following: $([ $bad = 0 ] && echo pass || echo FAIL)"
exit $bad
