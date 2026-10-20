#!/usr/bin/env python3
import os,sys,subprocess,json,hashlib
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-r4-transport2-20261021')
name,pattern,seconds=sys.argv[1:4]
os.chdir(H/'crate')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(H/'target'),CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(name+'-reservation.json'))],check=True)
(H/(name+'-inputs.json')).write_text(json.dumps(dict(source_revision=(H/'source-revision.txt').read_text().strip(),source_sha256=hashlib.sha256((H/'crate/src/lib.rs').read_bytes()).hexdigest(),source_cut=json.loads((H/'crate/source-cut.json').read_text()),command=['cargo','kani','--harness',pattern]),indent=2)+'\n')
cmd=['cargo','kani','--harness',pattern,'-Z','unstable-options','--output-format','terse','--cbmc-args','--unwinding-assertions']
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/name),'Kani compilation then '+pattern+' bounded single-step comparison; no dense arithmetic; timeout '+seconds+'s','--','timeout',seconds,*cmd]))
