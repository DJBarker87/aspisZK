"""Host-only extraction of this job's owned effect interface."""
from pathlib import Path
import subprocess,os,json,hashlib,time
R=Path('/home/dombarker/project-offloads/codex-cx-prover-commit49-20261022')
CHARON='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
AENEAS='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
os.chdir(R/'inactive-owner')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_BUILD_JOBS='4',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
def run(name,cmd):
 start=time.monotonic()
 while True:
  caps=[]
  for p in Path('/sys/fs/cgroup').rglob('memory.max'):
   try:
    v=p.read_text().strip()
    if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append({'path':str(p.parent),'bytes':int(v)})
   except OSError:pass
  if sum(x['bytes'] for x in caps)+8*2**30<=55*2**30:break
  assert time.monotonic()-start<600, 'reservation hold, no tool launched'
  print('Reservation hold: waiting for 8 GiB scope, no extraction launched',flush=True)
  time.sleep(15)
 (R/(name+'-inputs.json')).write_text(json.dumps(dict(source_sha256=hashlib.sha256(Path('lib.rs').read_bytes()).hexdigest(),reservations=caps,tools={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in [CHARON,AENEAS]}),indent=2)+'\n')
 subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'harness/capped.py'),str(R/'receipts'/name),'Optimized compilation and extraction of explicit-state digest, no arithmetic elimination','--',*cmd],check=True)
(R/'extraction').mkdir(exist_ok=True)
run('inactive-owner-charon-v1',[CHARON,'cargo','--preset','aeneas','--start-from','crate::owned','--mir','built','--sysroot','default','--dest-file',str(R/'extraction/inactive-owner49.llbc'),'--','--release','--lib','--jobs','4'])
data=json.loads((R/'extraction/inactive-owner49.llbc').read_text());assert not data['has_errors']
run('inactive-owner-aeneas-v1',[AENEAS,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1InactiveOwner49','-dest',str(R/'extraction/inactive-owner'),'-subdir','AspisR1InactiveOwner49','-split-files','-emit-json',str(R/'extraction/inactive-owner49.llbc')])
