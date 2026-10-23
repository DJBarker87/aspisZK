from pathlib import Path
import os,sys,subprocess,json,hashlib,time
H=Path('/home/dombarker/project-offloads/codex-cx-real-r3-20261023');E=H/'evidence';N=E/'RealR3_native'
name,harness=sys.argv[1:];os.chdir(N)
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(H/'kani-target'),RUSTFLAGS='-C opt-level=3 -C link-arg=-Wl,--threads=4')
def reservations():
 caps=[]
 for p in Path('/sys/fs/cgroup').rglob('memory.max'):
  try:
   v=p.read_text().strip()
   if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append({'path':str(p.parent),'bytes':int(v)})
  except OSError:pass
 return caps
caps=reservations();holds=[]
while sum(x['bytes'] for x in caps)+8*2**30>55*2**30:
 holds.append({'utc':time.time(),'reservations':caps})
 (E/(name+'-reservation-holds.json')).write_text(json.dumps(holds,indent=2)+'\n')
 print('Reservation hold:',sum(x['bytes'] for x in caps)/2**30,'+ 8 GiB > 55',flush=True)
 time.sleep(20);caps=reservations()
snap=E/'snapshots'/name;snap.mkdir(parents=True,exist_ok=False)
inputs={}
for p in N.rglob('*'):
 if p.is_file() and p.name!='Cargo.lock':
  rel=p.relative_to(N);q=snap/(str(rel)+'.txt');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());inputs[str(rel)]=hashlib.sha256(p.read_bytes()).hexdigest()
(E/(name+'-inputs.json')).write_text(json.dumps({'hashes':inputs,'reservations':caps,'source_revision':(H/'revision.txt').read_text().strip()},indent=2)+'\n')
cmd=['cargo','kani','-Z','stubbing','-Z','unstable-options','--no-assertion-reach-checks','--harness-timeout','180','-j','4','--output-format','terse','--exact','--harness',harness]
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(E/'RealR3_capped.py'),str(E/'receipts'/name),'Optimized Kani compilation followed by scalar emission control/bytes comparison; no elimination','--',*cmd]).returncode)
