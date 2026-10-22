from pathlib import Path
import subprocess,sys,json,hashlib
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit47-20261022'
name,harness=sys.argv[1:3]
(E/'pins'/f'{name}-inputs.json').write_text(json.dumps({str(p.relative_to(E)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (E/'native').rglob('*') if p.is_file()},indent=2)+'\n')
code='''from pathlib import Path
import os,subprocess,json
H=Path(%r)
caps=[]
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
 try:
  v=p.read_text().strip()
  if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
 except OSError:pass
assert sum(c['bytes'] for c in caps)+8*2**30<=55*2**30,caps
(H/(%r+'-reservations.json')).write_text(json.dumps(caps,indent=2)+'\\n')
os.chdir(H/'native')
env=os.environ|dict(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_BUILD_JOBS='4',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
raise SystemExit(subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/%r),'Time expected in symbolic CBMC field/codec checking, no arithmetic aggregation','--','timeout','180','cargo','kani','-Z','unstable-options','-j','4','--harness',%r,'--output-format','terse','--cbmc-args','--unwinding-assertions'],env=env).returncode)
'''%(H,name,name,harness)
subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,check=True)
