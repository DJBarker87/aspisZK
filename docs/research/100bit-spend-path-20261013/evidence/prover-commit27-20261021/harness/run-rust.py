from pathlib import Path
import subprocess,sys,json,hashlib
E=Path(__file__).resolve().parent.parent
R='/home/dombarker/project-offloads/codex-cx-prover-commit27-20261021'
name,harness=sys.argv[1:3]
snap=E/'rust-sources'/name;snap.mkdir(parents=True,exist_ok=False)
pins={}
for src,dest in [('oracle27.rs','lib.rs'),('effect27.rs','effect.rs')]:
 p=E/'harness'/src;(snap/(src+'.txt')).write_bytes(p.read_bytes())
 pins[src]=hashlib.sha256(p.read_bytes()).hexdigest()
 subprocess.run(['scp',str(p),'dombarker@100.108.41.90:'+R+'/oracle/src/'+dest],check=True)
(E/(name+'-inputs.json')).write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources=pins),indent=2)+'\n')
code='''from pathlib import Path
import subprocess,os,json
R=Path(%r)
caps=[]
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
 try:
  v=p.read_text().strip()
  if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
 except OSError:pass
assert sum(x['bytes'] for x in caps)+8*2**30<=55*2**30,caps
(R/(%r+'-reservations.json')).write_text(json.dumps(caps,indent=2)+'\\n')
os.chdir(R/'oracle')
env=os.environ|dict(RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4')
raise SystemExit(subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'harness/capped.py'),str(R/'receipts'/%r),'Per-call RefCell check; expected time in CBMC; verified equality contract; no arithmetic elimination','--','timeout','90','/home/dombarker/.cargo/bin/cargo','kani','-j','4','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness',%r,'--output-format','terse','--cbmc-args','--unwinding-assertions'],env=env).returncode)
'''%(R,name,name,harness)
subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,check=True)
