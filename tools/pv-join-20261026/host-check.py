"""One charged target through the unchanged restored launcher; capture receipts.
No launcher, environment, barrier, caps or shared library profile is modified.
"""
from pathlib import Path
import subprocess,sys,json,hashlib,re,datetime,time,shlex
root=Path(__file__).resolve().parents[2];e=root/'evidence/pv-join-20261026/resume'
a=int(sys.argv[1]);m=sys.argv[2];assert 35300<=a<=35599 and re.fullmatch(r'[A-Za-z0-9_./]+',m)
m=m.replace('.','/');assert m not in {'R1Z/EventsR1P2','R1Z/SimCostOuterRetry6'}
charged=sum(json.loads(p.read_text()).get('charged_lean_attempts',0) for p in e.glob('*-receipt.json'))
assert charged<100, ('resume compile budget exhausted',charged)
own='/home/dombarker/project-offloads/codex-pv-join-20261026';J='/home/dombarker/project-offloads/aspis-joint-20261019';H='/home/dombarker/project-offloads/r1-privacy-build-integration-20261019';T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence';host='dombarker@100.108.41.90'
def ssh(cmd):return subprocess.run(['ssh','-o','BatchMode=yes',host,cmd],text=True,capture_output=True)
def py(code):return subprocess.run(['ssh','-o','BatchMode=yes',host,'python3 -'],input=code,text=True,capture_output=True)
assert not (e/f'{a}-receipt.json').exists()
# Use the exact reservation script selected by EJR_build_host.py in the restored handoff.
q=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2x-20261023/S2X_reservation.py {own}/receipts/{a}-admission.json > {own}/receipts/{a}-admission.log 2>&1; code=$?; cat {own}/receipts/{a}-admission.log; exit $code')
z=ssh(f'cat {own}/receipts/{a}-admission.json');(e/f'{a}-admission.json').write_text(z.stdout)
try:admission=json.loads(z.stdout)
except Exception:raise RuntimeError(q.stdout+q.stderr+z.stderr)
if not admission.get('allowed'):
 (e/f'{a}-refusal.json').write_text(json.dumps(dict(attempt=a,target=m,compiler_invoked=False,charged_lean_attempts=0,admission=admission,stdout=q.stdout,stderr=q.stderr),indent=2)+'\n');print(a,m,'REFUSED',flush=True);raise SystemExit(78)
local=root/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
if not local.is_file() and m.startswith('R1Z/ProverRwFull'):
 local=root/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/(m.split('/')[-1]+'.lean')
if local.is_file():content=local.read_bytes();origin=str(local.relative_to(root))
else:
 catalog=json.loads((e/'source-preflight.json').read_text())['modules'];entry=catalog[m.replace('/','.')];o=entry['origin'];content=subprocess.check_output(['git','show',o['revision']+':'+o['path']],cwd=root);origin=o
sha=hashlib.sha256(content).hexdigest();snapshot=e/f'{a}.lean.txt';snapshot.write_bytes(content)
remote=f'{own}/target.lean';subprocess.run(['scp',str(snapshot),host+':'+remote],check=True,capture_output=True)
taskrev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
if isinstance(origin,str):
 old=subprocess.run(['git','show',taskrev+':'+origin],cwd=root,capture_output=True)
 committed=old.returncode==0 and old.stdout==content
 rev=taskrev+('' if committed else '+uncommitted')
else:
 committed=True;rev=origin['revision']
code=f'''from pathlib import Path
import json,hashlib,shutil
J=Path({J!r});H=Path({H!r});O=Path({own!r});m={m!r};a={a};expected={sha!r}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=O/'target.lean';dst=J/'sources'/(m+'.lean');obj=J/'objects'/(m+'.olean')
old=sha(dst) if dst.is_file() else None
if old and old!=expected and not m.startswith('R1Z/PV_Join_'):
 print(json.dumps(dict(guard='shared source differs; not overwritten',target=m,expected=expected,actual=old)));raise SystemExit(66)
b=O/('before-'+str(a));b.mkdir(exist_ok=True)
for p in [dst,obj]:
 if p.is_file():shutil.copy2(p,b/p.name)
dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
env=json.loads((H/'env/J.json').read_text());paths=[J/'objects']+[Path(p) for p in env['LEAN_PATH'].split(':')];ds=[]
for line in src.read_text().splitlines():
 if line.startswith('import '):
  for mod in line[7:].split():
   rel=mod.replace('.','/');base=next((p for p in paths if (p/rel.split('/')[0]).is_dir()),None);p=base/(rel+'.olean') if base else None
   ds.append(dict(module=mod,path=str(p) if p and p.is_file() else None,sha256=sha(p) if p and p.is_file() else None))
fp=hashlib.sha256(json.dumps(ds,sort_keys=True).encode()).hexdigest();(O/'receipts'/f'{{a}}-fp.txt').write_text(fp)
x=dict(attempt=a,module=m,source_sha256=expected,source_revision={rev!r},source_origin={origin!r},deps=ds,deps_fingerprint=fp,old_source_sha256=old,command=[str(H/'tools/run-joint.sh'),str(a),m,'J','7000','8',fp],caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000))
(O/'receipts'/f'{{a}}-input.json').write_text(json.dumps(x,indent=2)+'\\n');print(json.dumps(x))
'''
p=py(code)
if p.returncode:
 (e/f'{a}-guard.json').write_text(json.dumps(dict(target=m,exit=p.returncode,stdout=p.stdout,stderr=p.stderr,compiler_invoked=False),indent=2)+'\n');print(a,m,'GUARD',p.stdout,p.stderr,flush=True);raise SystemExit(p.returncode)
x=json.loads(p.stdout);x.update(task_revision=taskrev,source_was_uncommitted=not committed,runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest());(e/f'{a}-input.json').write_text(json.dumps(x,indent=2)+'\n')
fp=x['deps_fingerprint'];cmd=f'{H}/tools/run-joint.sh {a} {m} J 7000 8 {fp} > {own}/receipts/{a}-launch.log 2>&1; code=$?; cat {own}/receipts/{a}-launch.log; exit $code'
print(a,m,'START',flush=True);start=time.monotonic();run=ssh(cmd);(e/f'{a}-launch.log').write_text(run.stdout+run.stderr)
raw=ssh(f'cat {T}/out-{a}.log').stdout;tim=ssh(f'cat {T}/time-{a}.log').stdout
(e/f'{a}-out.log').write_text(raw);(e/f'{a}-time.log').write_text(tim)
ec=re.search(r'^exit=(\d+)',raw,re.M)
if not ec:
 (e/f'{a}-refusal.json').write_text(json.dumps(dict(target=m,launcher_exit=run.returncode,stdout=run.stdout,stderr=run.stderr,compiler_invoked=False,charged_lean_attempts=0),indent=2)+'\n');print(a,m,'LAUNCH REFUSED',run.stdout,flush=True);raise SystemExit(78)
reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",raw)
bad=[]
for report in reports:
 if 'depends on axioms:' in report:
  axioms={s.strip() for s in report.split('depends on axioms: [')[1].split(']')[0].split(',')}
  if not axioms <= {'propext','Classical.choice','Quot.sound'}:bad.append(report)
exitcode=int(ec[1]);peak=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tim);swap=re.search(r'Swaps:\s*(\d+)',tim);wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)',tim)
x.update(compiler_invoked=True,charged_lean_attempts=1,exit_status=exitcode,validation_exit=exitcode or (90 if bad or 'sorryAx' in raw else 0),wall=wall[1] if wall else None,outer_wall_seconds=time.monotonic()-start,peak_rss_kib=int(peak[1]) if peak else None,swaps=int(swap[1]) if swap else None,print_axioms=reports,rejected_axioms=bad,errors=[line for line in raw.splitlines() if 'error:' in line],utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
if x['validation_exit']==0:
 cachecode=f'''from pathlib import Path
import shutil,json,hashlib
O=Path({own!r});J=Path({J!r});m={m!r};a={a};p=J/'objects'/(m+'.olean');out=O/'lean-objects'/(m+'.olean');out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,out)
x=dict(module=m,object_path=str(out),object_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),object_bytes=out.stat().st_size,provenance='compiled by own attempt '+str(a),receipt=str(O/'receipts'/f'{{a}}-input.json'));print(json.dumps(x))
'''
 cache=py(cachecode)
 if cache.returncode==0:x['private_cache']=json.loads(cache.stdout)
(e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n')
print(a,m,'EXIT',x['exit_status'],'VALID',x['validation_exit'],'WALL',x['wall'],'RSS',x['peak_rss_kib'],'SWAP',x['swaps'],'AXIOMS',len(reports),flush=True)
for err in x['errors'][:3]:print(err,flush=True)
raise SystemExit(x['validation_exit'])
