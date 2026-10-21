#!/usr/bin/env python3
"""Aggregate distinct constant-index SINGLE-STEP roots; never whole loops."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
env=dict(os.environ,CARGO_TARGET_DIR=str(R/'mutable-slot-target'),S7_TIMEOUT='480',S7_EXPECTED='Cached optimized compilation, then eight independent constant-index SINGLE accumulator-row transition SAT checks in two waves of four. Slot 00 predecessor passed in 143.454 s. Expected solver time, not whole-loop unrolling or dense elimination. Memory cap unchanged.')
for first in range(1,64,8):
 indices=list(range(first,min(first+8,64)))
 attempt=f'accumulator-slots-{indices[0]:02}-{indices[-1]:02}'
 args=['sh',str(R/'tools/s7-kani2-20261021/launch.sh'),attempt,'--exact']
 for i in indices:args+=['--harness',f'certificate::accumulator_mutable_slot_{i:02}']
 print('Starting '+attempt,flush=True)
 subprocess.run(args,env=env,check=True)
