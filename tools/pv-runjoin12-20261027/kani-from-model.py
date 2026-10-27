"""One charged check of an inlined Kani-generated model, with unchanged CBMC flags."""
from pathlib import Path
import subprocess,json,sys,shlex,hashlib,atexit
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026';host='dombarker@100.108.41.90'
atexit.register(lambda:subprocess.run([sys.executable,str(R/'tools/pv-runjoin12-20261027/tally.py')],stdout=subprocess.DEVNULL))
number=int(sys.argv[1]);suffix=sys.argv[2];assert number in [2,6,8,10]
inv=E/'kani-invocations.jsonl';old=[json.loads(x) for x in inv.read_text().splitlines()];assert len(old)<12 and number not in [x['number'] for x in old]
name=f'pv12-runjoin-kani-{number:02d}';out=H+'/evidence/'+name;model=H+'/evidence/pv12-goto-inline-01.out'
def ssh(s):return subprocess.run(['ssh','-o','BatchMode=yes',host,s],capture_output=True,text=True)
res=H+'/evidence/'+name+'-reservation-'+suffix
r=ssh(f'python3 {H}/reservation-existing.py {res}.json > {res}.log 2>&1\ncat {res}.log');(E/(name+'-reservation-'+suffix+'.log')).write_text(r.stdout+r.stderr);admission=json.loads(r.stdout.strip().splitlines()[-1])
if not admission['allowed']:
 (E/(name+'-refusal-'+suffix+'.json')).write_text(json.dumps(admission,indent=2)+'\n');print('RESERVATION REFUSED',admission,flush=True);sys.exit(78)
for ext in ['json','log']:subprocess.run(['scp','-q',f'{host}:{res}.{ext}',str(E/(name+'-reservation-'+suffix+'.'+ext))],check=True)
subprocess.run(['scp','-q',str(R/'tools/pv-runjoin12-20261027/kani-receipt.py'),f'{host}:{H}/evidence/pv12-model-receipt.py'],check=True)
pins=ssh('python3 -c '+shlex.quote('import pathlib,hashlib,json;print(json.dumps({p:dict(sha256=hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest(),size=pathlib.Path(p).stat().st_size) for p in '+repr([model,'/home/dombarker/.kani/kani-0.67.0/bin/cbmc','/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument'])+'}))'));assert pins.returncode==0
backend=['/home/dombarker/.kani/kani-0.67.0/bin/cbmc',model,'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','25','--sat-solver','cadical','--slice-formula','--unwinding-assertions','--verbosity','9','--json-ui']
command=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','PV8_SOURCE_DIR='+H+'/frozen','python3',H+'/evidence/pv12-model-receipt.py',out,'timeout','900','taskset','--cpu-list','0-3',*backend]
origin=next(x for x in old if x['number']==7)
record=dict(number=number,harness=origin['harness'],source_revision=origin['source_revision'],worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=command,source_sha256=origin['source_sha256'],stubs=[],verified_stubs=[],mode='Kani-generated model, source-helper inlining only; direct bundled CBMC with observed Run07 options',rust_configuration='exact retained Run07 compilation; no Rust compiler option changed',model_and_tool_pins=json.loads(pins.stdout),expected_time='one named actual-source root-helper aggregation in CBMC; no Rust compilation')
with inv.open('a') as f:f.write(json.dumps(record)+'\n')
print('CHARGED KANI MODEL CHECK',number,flush=True)
r=ssh(shlex.join(command));(E/(name+'-scope.log')).write_text(r.stdout+r.stderr)
p=E/name;p.mkdir(exist_ok=True)
for f in ['out.log','receipt.json']:subprocess.run(['scp','-q',f'{host}:{out}/{f}',str(p/f)],check=True)
d=json.loads((p/'receipt.json').read_text());d.update(record)
try:
 data=json.loads((p/'out.log').read_text());statuses=[x['cProverStatus'] for x in data if 'cProverStatus' in x];d['cbmc_status']=statuses
 d['accepted']=d['exit']==0 and statuses==['success']
except json.JSONDecodeError:d['accepted']=False
(p/'receipt.json').write_text(json.dumps(d,indent=2)+'\n')
state=ssh(f'systemctl --user show {name}.scope -p ActiveState -p SubState');assert 'ActiveState=active' not in state.stdout;(E/(name+'-ended.log')).write_text(state.stdout+state.stderr)
print(json.dumps({k:d.get(k) for k in ['exit','wall_seconds','peak_rss_bytes','swaps','cbmc_status','accepted']}),flush=True);sys.exit(r.returncode)
