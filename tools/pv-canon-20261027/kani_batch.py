"""Six finite optimized control gates, sequential in one admitted capped scope."""
from pathlib import Path
import subprocess,json,sys,time,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-canon-20261027';H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-canon-20261027';tp=E/'tally.json';t=json.loads(tp.read_text());start=t['kani']+1;assert start<=6
names=['CLI-rejected-before-compilation','op121_block_indices','op121_descending_blocks','interpolation_sample_ctor','interpolation_basis_indices','semantic_round_tags'];tag='kani-batch-'+str(time.time_ns());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();sha=hashlib.sha256((R/'tools/pv-canon-20261027/control/src/lib.rs').read_bytes()).hexdigest()
precode="from pathlib import Path; import subprocess; O=Path("+repr(D)+")/'preflight'/"+repr(tag)+"; O.mkdir(parents=True); r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(O/'reservation.json')],stdout=open(O/'reservation.log','w'),stderr=subprocess.STDOUT); print((O/'reservation.log').read_text()); raise SystemExit(r.returncode)"
r=subprocess.run(['ssh',H,'python3 -'],input=precode,text=True,capture_output=True);(E/(tag+'-reservation.log')).write_text(r.stdout+r.stderr)
if r.returncode:print(r.stdout+r.stderr+'UNCHARGED; cooldown 180s');raise SystemExit(r.returncode)
subprocess.run(['ssh',H,'mkdir -p '+D+'/control/src'],check=True)
for f in ['Cargo.toml','src/lib.rs']:subprocess.run(['scp',str(R/'tools/pv-canon-20261027/control'/f),H+':'+D+'/control/'+f],check=True,stdout=subprocess.DEVNULL)
worker='''from pathlib import Path
import os,json,time,subprocess
D=Path(DIR);names=NAMES
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3',RUSTFLAGS='-C opt-level=3')
for n in range(START,7):
 O=D/'receipts'/(TAG+'-'+str(n));O.mkdir(parents=True);name='checks::'+names[n-1]
 cmd=['timeout','180','taskset','--cpu-list','0-3','/home/dombarker/.cargo/bin/cargo','kani','--exact','--harness',name,'-j','4','--output-format','terse','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
 started=time.monotonic();r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=D/'control',stdout=open(O/'out.log','w'),stderr=subprocess.STDOUT)
 meta=dict(number=n,target=name,exit=r.returncode,wall_seconds=time.monotonic()-started,revision=REVISION,source_sha256=SOURCEHASH,command=cmd,phase='optimized tiny control/indexing model, no field arithmetic',print_axioms='N/A Kani',time_log=(O/'time.log').read_text());(O/'receipt.json').write_text(json.dumps(meta,indent=2));print(str(n)+' '+name+' exit='+str(r.returncode),flush=True)
 if r.returncode:print((O/'out.log').read_text(),flush=True);break
'''.replace('DIR',repr(D)).replace('NAMES',repr(names)).replace('START',str(start)).replace('TAG',repr(tag)).replace('REVISION',repr(rev)).replace('SOURCEHASH',repr(sha))
subprocess.run(['ssh',H,'cat > '+D+'/'+tag+'.py'],input=worker,text=True,check=True)
code='''from pathlib import Path
import subprocess
D=Path(DIR);G=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy');O=D/'preflight'/TAG
r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'barrier.json'),'python3',str(D/(TAG+'.py'))]);raise SystemExit(r.returncode)
'''.replace('DIR',repr(D)).replace('TAG',repr(tag))
r=subprocess.run(['ssh',H,'python3 -'],input=code,text=True,capture_output=True);print(r.stdout+r.stderr);(E/(tag+'-scope.log')).write_text(r.stdout+r.stderr)
for n in range(start,7):
 subprocess.run(['scp','-r',H+':'+D+'/receipts/'+tag+'-'+str(n),str(E)],capture_output=True)
 rp=E/(tag+'-'+str(n))/'receipt.json'
 if rp.exists():
  t=json.loads(tp.read_text());t['kani']+=1;tp.write_text(json.dumps(t,indent=2)+'\n')
