#!/usr/bin/env python3
import os,sys,subprocess,json,hashlib
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s2-kani-20261021')
name,pattern,seconds=sys.argv[1:4]
crate=H/('linked' if name.startswith('linked-') else 'crate');os.chdir(crate)
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(H/'target'),CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(name+'-reservation.json'))],check=True,stdout=subprocess.DEVNULL)
source=(crate/'src/lib.rs').read_bytes();snapshots=H/'source-snapshots';snapshots.mkdir(exist_ok=True)
(snapshots/(hashlib.sha256(source).hexdigest()+'.rs.txt')).write_bytes(source)
cmd=['cargo','kani','-j','4','--harness',pattern,'-Z','unstable-options','--output-format','terse','--cbmc-args','--unwinding-assertions']
(H/(name+'-inputs.json')).write_text(json.dumps(dict(source_revision=(H/'source-revision.txt').read_text().strip(),source_sha256=hashlib.sha256(source).hexdigest(),source_cut=json.loads((crate/'source-cut.json').read_text()),command=cmd),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/name),'Kani compilation and bounded '+pattern+' comparison; no dense arithmetic; timeout '+seconds+'s','--','timeout',seconds,*cmd]))
