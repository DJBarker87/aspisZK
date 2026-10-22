#!/usr/bin/env python3
import subprocess,json,hashlib,sys
from pathlib import Path
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit46-20261022'
name=sys.argv[1]
assert name in ['program-one-transition-v1','program-one-transition-v2']
files=[E/'harness/lib.rs',E/'harness/owned.rs',E/'harness/Cargo.toml']
(E/'pins'/f'{name}-inputs.json').write_text(json.dumps(dict(source_revision=(E/'pins/revision.txt').read_text().strip(),sources={str(p.relative_to(E)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}),indent=2)+'\n')
code='''from pathlib import Path
import subprocess,os,json
H=Path(%r)
caps=[]
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
 try:
  v=p.read_text().strip()
  if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
 except OSError:pass
assert sum(x['bytes'] for x in caps)+8*2**30<=55*2**30,caps
(H/(%r+'-inputs.json')).write_text(json.dumps(dict(reservations=caps),indent=2)+'\\n')
os.chdir(H/'harness')
env=os.environ|dict(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4')
raise SystemExit(subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/%r),'Per-call RefCell control against owned state-passing reference; time expected in CBMC, not arithmetic elimination','--','timeout','180','/home/dombarker/.cargo/bin/cargo','kani','-Z','unstable-options','-j','4','--harness','program_one_transition','--output-format','terse','--cbmc-args','--unwinding-assertions'],env=env).returncode)
'''%(H,name,name)
subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,check=True)
