"""Recover the precise error hidden by Kani terse status 6; same named cell."""
from pathlib import Path
import subprocess,hashlib,json,os,time
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022')
program=next((H/'kani-lane2-target/kani/x86_64-unknown-linux-gnu/debug/deps').glob('*13short_records.out'))
CBMC=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');solver=CBMC.parent/'kissat'
os.environ.update(PATH=str(CBMC.parent)+':/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTFLAGS='-C link-arg=-Wl,--threads=4')
while True:
 caps=[]
 for p in Path('/sys/fs/cgroup').rglob('memory.max'):
  try:
   v=p.read_text().strip()
   if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
  except OSError:pass
 if sum(x['bytes'] for x in caps)+8*2**30<=55*2**30:break
 print('Reservation hold',flush=True);time.sleep(30)
name='row14-status6-diagnostic'
(H/(name+'-inputs.json')).write_text(json.dumps(dict(source_revision=(H/'revision.txt').read_text().strip(),reservations=caps,program=str(program),pins={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size_bytes=p.stat().st_size) for p in [program,CBMC,solver]},purpose='Missing evidence artifact: recover raw JSON diagnostic masked by Kani terse exit 6; absolute external-solver path'),indent=2)+'\n')
cmd=[str(CBMC),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--unwind','40','--external-sat-solver',str(solver),'--slice-formula','--unwinding-assertions','--object-bits','10',str(program),'--verbosity','9','--json-ui']
raise SystemExit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Raw CBMC diagnostic for one field-bearing iteration; no Rust compilation or dense arithmetic','--','timeout','600',*cmd]).returncode)
