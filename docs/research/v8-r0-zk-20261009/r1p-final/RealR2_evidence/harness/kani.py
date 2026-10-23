from pathlib import Path
import subprocess,sys,json,hashlib
E=Path(__file__).resolve().parent.parent
name,harness=sys.argv[1:3]
folder=sys.argv[3] if len(sys.argv)>3 else 'native'
assert folder in ['native','sampler']
assert name.startswith('RealR2_')
H='/home/dombarker/project-offloads/codex-cx-real-r2-20261023'
pins={str(p.relative_to(E)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (E/folder).rglob('*') if p.is_file()}
(E/(name+'-inputs.json')).write_text(json.dumps(pins,indent=2)+'\n')
code='''from pathlib import Path
import os,subprocess,json,time
H=Path(%r)
def reservations():
 caps=[]
 for p in Path('/sys/fs/cgroup').rglob('memory.max'):
  try:
   v=p.read_text().strip()
   if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
  except OSError:pass
 return caps
caps=reservations()
while sum(c['bytes'] for c in caps)+8*2**30>55*2**30:
 print('Reservation hold: no Kani launched',flush=True)
 time.sleep(30);caps=reservations()
(H/(%r+'-reservations.json')).write_text(json.dumps(caps,indent=2)+'\\n')
os.chdir(H/%r)
env=os.environ|dict(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_BUILD_JOBS='4',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
raise SystemExit(subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/%r),'Time expected in Kani compilation and symbolic seed-frame checks; no arithmetic aggregation','--','timeout','180','cargo','kani','-Z','function-contracts','-Z','stubbing','-Z','unstable-options','-j','4','--exact','--harness',%r,'--output-format','terse','--cbmc-args','--unwinding-assertions'],env=env).returncode)
'''%(H,name,folder,name,harness)
raise SystemExit(subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True).returncode)
