"""NIH-owned input client; unchanged S2W launcher and admission infrastructure."""
from pathlib import Path
import base64, json, subprocess, sys, time, hashlib, shlex, re, os, atexit
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-terminal6-20261110'
a=sys.argv[1]; assert re.fullmatch(r'NLH_[LKE][0-9]{3}',a)
x=json.loads((E/(a+'.json')).read_text()); assert x['attempt']==a
assert 1<=int(a[-3:])
budget={'L':140,'K':50,'E':0}[a[4]]
charged=sum(json.loads(row)['attempt'][4]==a[4] for row in (E/'NLH_ATTEMPTS.jsonl').read_text().splitlines())
assert charged<budget, 'Authorized scope budget exhausted'
if x['command'][:2]==['python3','NLH_gate.py']:assert x['command'][2]==a+'.json','Stale gate configuration'
assert not (E/a/'receipt.json').exists(), 'Never resubmit'
guard=E/'NLH_CLIENT_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
  with (E/'NLH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Recover read-only; never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for disk_retry in range(7):
 r=ssh("python3", "import shutil,json,subprocess,pathlib; p=pathlib.Path('/home/dombarker/project-offloads/codex-cx-terminal6-20261110'); print(json.dumps(dict(free=shutil.disk_usage(p.parent).free,workspace_bytes=int(subprocess.check_output(['du','-sb',str(p)]).split()[0]) if p.exists() else 0)))")
 assert r.returncode==0,r.stderr
 disk=json.loads(r.stdout);disk.update(attempt=a,retry=disk_retry,minimum=40_000_000_000)
 assert disk['workspace_bytes']<30_000_000_000, 'STOP own workspace30GBcap'
 with (E/'NLH_DISK.jsonl').open('a') as f:f.write(json.dumps(disk)+'\n')
 if disk['free']>=40_000_000_000:break
 if disk_retry==6:raise RuntimeError('STOP disk floor after six10minute waits')
 print('disk floor wait10minutes',flush=True)
 for _ in range(10):time.sleep(60)
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
assert __import__('shutil').disk_usage(b).free >= 40_000_000_000, 'DISK_BELOW_40GB'
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r};print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  print('reservation wait',flush=True);time.sleep(60);time.sleep(60);time.sleep(60);continue
 raise RuntimeError('STOP admission')
x.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True)
assert all((E/n).is_file() for n in x['sources']), 'Missing required validation input'
files={n:(base64.b64encode((E/n).read_bytes()).decode() if n.endswith('.xz') else (E/n).read_text()) for n in x['sources'] if (E/n).is_file()}
files[a+'.json']=json.dumps(x)
r=ssh('python3',f'''from pathlib import Path
import base64,json,shutil,hashlib,re,os,subprocess
b=Path({B!r});w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 if not (b/n).exists():shutil.copyfile(w/n,b/n)
for n,t in json.loads({json.dumps(files)!r}).items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);(p.write_bytes(base64.b64decode(t)) if n.endswith('.xz') else p.write_text(t))
for n in ['NLH_objects','NLH_generated','NLH_tmp','NLH_native']:(b/n).mkdir(exist_ok=True)
exec((b/'NLH_seed.py').read_text())
for suffix in []:
 if (b/('NLH_'+suffix)).is_file():(b/('NKI_'+suffix)).write_bytes((b/('NLH_'+suffix)).read_bytes())
p=b/{(a+'.json')!r};x=json.loads(p.read_text());roots=x.get('env',{{}}).get('LEAN_PATH','').split(':');rels=set();pins={{}}
if x['kind']=='lean':
 probe=subprocess.run(['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','printenv','LEAN_PATH'],cwd=b,env=dict(os.environ,**x.get('env',{{}})),capture_output=True,text=True)
 assert probe.returncode==0,probe.stderr
 roots=probe.stdout.strip().split(':');x['effective_lean_path']=roots
else:x['effective_lean_path']=roots
roots=[str((b/root).resolve()) if not Path(root).is_absolute() else root for root in roots]
x['library_pin_selection']='actual lake env LEAN_PATH for compiler; direct env for native auditor'

if x['kind'] in ['lean','audit']:
 for root in roots:
  for stem in ['Aeneas','AeneasMeta']:
   q=Path(root)/stem
   if q.is_dir():rels.update(str(z.relative_to(root)) for z in q.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
   if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
 if x['kind']=='lean':
  for n in re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M):rels.add(n.replace('.','/')+'.olean')
 else:
  modules=x.get('audit_modules',[])
  for n in modules:rels.add(n.replace('.','/')+'.olean')
 for rel in sorted(rels):
  q=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert q is not None,rel
  for z in [q,Path(str(q)+'.private'),Path(str(q)+'.server'),q.with_suffix('.ir')]:
   if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
if (b/'NLH_priority').exists():
 for q in (b/'NLH_priority').iterdir():
  if q.is_file():pins[str(q)]={{'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins}};p.write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=[str(p.relative_to(b)) for p in (b/{a!r}).rglob('*') if p.is_file()]+[{(a+'.json')!r}]+{x.get('collect',[])!r}
for pattern in {x.get('collect_globs',[])!r}:names += [str(p.relative_to(b)) for p in b.glob(pattern) if p.is_file()]
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).is_file() and not n.endswith('.xz')}}))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; recover, never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NLH_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
