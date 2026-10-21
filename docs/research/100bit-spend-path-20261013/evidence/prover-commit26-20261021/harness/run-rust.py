"""One capped, reservation-checked Kani gate with exact source identity."""
from pathlib import Path
import hashlib,json,subprocess,sys
E=Path(__file__).resolve().parent.parent
name,harness,seconds=sys.argv[1:4]
R='/home/dombarker/project-offloads/codex-cx-prover-commit26-20261021'
source=E/'harness/query26.rs'
identity=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),harness=harness)
(E/(name+'-inputs.json')).write_text(json.dumps(identity,indent=2)+'\n')
code='''from pathlib import Path
import subprocess,time,os,json
R=Path(%r)
def total():
 caps=[]
 for p in Path('/sys/fs/cgroup').rglob('memory.max'):
  try:
   if p.read_text().strip()!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(int(p.read_text()))
  except OSError:pass
 return sum(caps)
start=time.monotonic()
while total()+8*2**30>55*2**30:
 print('Waiting for Rust reservation:',total()/2**30,flush=True)
 assert time.monotonic()-start<600
 time.sleep(15)
print('Reservation before Rust:',total()/2**30,flush=True)
os.chdir(R/'query')
env=os.environ|dict(RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4')
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'harness/capped.py'),str(R/'receipts'/%r),'Length-specialised Rust library membership proof; expected time in CBMC, no arithmetic elimination','--','timeout',%r,'/home/dombarker/.cargo/bin/cargo','kani','-j','4','-Z','unstable-options','--no-assertion-reach-checks','--exact','--harness',%r,'--output-format','terse','--cbmc-args','--unwinding-assertions']
raise SystemExit(subprocess.run(cmd,env=env).returncode)
'''%(R,name,seconds,harness)
subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,check=True)
