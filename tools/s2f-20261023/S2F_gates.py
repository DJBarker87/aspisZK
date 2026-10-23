#!/usr/bin/env python3
from pathlib import Path
import subprocess,json
T=Path(__file__).parent
names=['S2F_checked_end_overflow','S2F_shape1','S2F_scan_leaf','S2F_proof_decision','S2F_range_split','S2F_checkpoint_length','S2F_shape2_clear','S2F_stage2_lengths','S2F_child_error_control','S2F_mapped_errors','S2F_exclusive_acquire','S2F_shared_acquire','S2F_shared_drop','S2F_exclusive_drop']
for num,name in enumerate(names,4):
 if num<8: continue
 r=subprocess.run(['python3',str(T/'S2F_attempt.py'),'kani',str(num),name])
 if r.returncode: raise SystemExit(r.returncode)
