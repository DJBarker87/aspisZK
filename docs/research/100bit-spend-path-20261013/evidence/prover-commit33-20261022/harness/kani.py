#!/usr/bin/env python3
import subprocess,os,sys,json,hashlib
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit33-20261022')
name,target=sys.argv[1:3]
os.chdir(H/'harness')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(H/'kani-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
caps=[]
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
 try:
  v=p.read_text().strip()
  if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
 except OSError:pass
assert sum(x['bytes'] for x in caps)+8*2**30<=55*2**30,caps
(H/(name+'-inputs.json')).write_text(json.dumps(dict(source_revision=(H/'revision.txt').read_text().strip(),hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (H/'harness').iterdir() if p.is_file()},reservations=caps),indent=2)+'\n')
cmd=['cargo','kani','--no-assertion-reach-checks','-j','4','--lib','--exact','--harness',target,'-Z','unstable-options','--output-format','terse','--cbmc-args','--unwinding-assertions','--object-bits','10']
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Kani compile then publication loop logic with sorted-list TrustedStd substitute; no finite-field arithmetic','--','timeout','600',*cmd]).returncode)
