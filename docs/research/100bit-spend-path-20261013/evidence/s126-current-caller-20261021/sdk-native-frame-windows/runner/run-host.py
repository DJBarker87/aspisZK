#!/usr/bin/env python3
from pathlib import Path
import os,json,subprocess,sys,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
name=sys.argv[1]
harness=sys.argv[2] if len(sys.argv)>2 else 'proofs::actual_sdk_stage1_binding'
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'target'),RUSTFLAGS='-C opt-level=3 -C overflow-checks=yes -C link-arg=-Wl,--threads=1')
os.chdir(H/'crate')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(name+'-admission.json'))],check=True)
cmd=['cargo','kani','--lib','--exact','--harness',harness,'-j','1','-Z','unstable-options','--output-format','terse','--harness-timeout','600','--cbmc-args','--unwinding-assertions']
(H/(name+'-input.json')).write_text(json.dumps(dict(command=cmd,source_sha256=hashlib.sha256((H/'crate/src/lib.rs').read_bytes()).hexdigest(),expected_time='Compilation followed by CBMC of named SDK stage1 control/borrow/copy harness, optimized Rust; no finite-field elimination'),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/name),'Optimized Kani compilation and named stage1 SDK/control harness; 600s CBMC timeout','--',*cmd]))
