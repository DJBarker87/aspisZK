from pathlib import Path
import os,sys,subprocess,json,hashlib,time
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023')
name,harness=sys.argv[1:]
os.chdir(H/'native-constructors')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(H/'kani-target'),RUSTFLAGS='-C opt-level=3 -C link-arg=-Wl,--threads=4')
while True:
 caps=[]
 for p in Path('/sys/fs/cgroup').rglob('memory.max'):
  try:
   v=p.read_text().strip()
   if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
  except OSError:pass
 if sum(x['bytes'] for x in caps)+8*2**30<=55*2**30:break
 print('Reservation hold; no native compiler invoked',flush=True)
 time.sleep(15)
s=H/'input-snapshots'/name;s.mkdir(parents=True,exist_ok=False)
for p in (H/'native-constructors').rglob('*'):
 if p.is_file():
  dest=s/(str(p.relative_to(H/'native-constructors'))+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
(H/(name+'-inputs.json')).write_text(json.dumps(dict(revision=(H/'revision.txt').read_text().strip(),hashes={str(p.relative_to(H/'native-constructors')):hashlib.sha256(p.read_bytes()).hexdigest() for p in (H/'native-constructors').rglob('*') if p.is_file()},reservations=caps),indent=2)+'\n')
cmd=['cargo','kani','-Z','stubbing','-Z','function-contracts','-Z','unstable-options','--no-assertion-reach-checks','--harness-timeout','180','-j','4','--output-format','terse','--exact','--harness',harness]
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Optimized Kani compilation and one selected adapter-output contract; no field elimination','--',*cmd]).returncode)
