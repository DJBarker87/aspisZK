"""NIH-owned input client; unchanged S2W launcher and admission infrastructure."""
from pathlib import Path
import base64, json, subprocess, sys, time, hashlib, shlex, re, os, atexit
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-terminal3-20261108'
a=sys.argv[1]; assert re.fullmatch(r'NJX_[LKE][0-9]{3}',a)
x=json.loads((E/(a+'.json')).read_text()); assert x['attempt']==a
assert 1<=int(a[-3:])
budget={'L':120,'K':70,'E':0}[a[4]]
charged=sum(json.loads(row)['attempt'][4]==a[4] for row in (E/'NJX_ATTEMPTS.jsonl').read_text().splitlines())
assert charged<budget, 'Authorized scope budget exhausted'
if x['command'][:2]==['python3','NJX_gate.py']:assert x['command'][2]==a+'.json','Stale gate configuration'
assert not (E/a/'receipt.json').exists(), 'Never resubmit'
guard=E/'NJX_CLIENT_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
  with (E/'NJX_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Recover read-only; never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
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
files={n:(base64.b64encode((E/n).read_bytes()).decode() if n.endswith('.xz') else (E/n).read_text()) for n in x['sources'] if (E/n).is_file()}
files[a+'.json']=json.dumps(x)
r=ssh('python3',f'''from pathlib import Path
import base64,json,shutil,hashlib,re
b=Path({B!r});w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 if not (b/n).exists():shutil.copyfile(w/n,b/n)
for n,t in json.loads({json.dumps(files)!r}).items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);(p.write_bytes(base64.b64decode(t)) if n.endswith('.xz') else p.write_text(t))
for n in ['NJX_objects','NJX_generated','NJX_tmp','NJX_native']:(b/n).mkdir(exist_ok=True)
manifest=json.loads((b/'NJX_PREDECESSOR_EXPORT.json').read_text());seed=b/'NJX_seed';seed.mkdir(exist_ok=True);records=[]
for entry in manifest['files']:
 src=Path(entry['path']);dst=seed/src.name
 assert hashlib.sha256(src.read_bytes()).hexdigest()==entry['sha256'],str(src)
 if not dst.exists():shutil.copyfile(src,dst)
 assert hashlib.sha256(dst.read_bytes()).hexdigest()==entry['sha256'],str(dst)
 records.append(dict(path=str(dst),sha256=entry['sha256'],bytes=dst.stat().st_size))
(b/'NJX_SEED.json').write_text(json.dumps(dict(files=records,total_bytes=sum(z['bytes'] for z in records))))


manifest2=json.loads((b/'NJX_NJO_EXPORT.json').read_text());seed2=b/'NJX_NJO_seed';seed2.mkdir(exist_ok=True);records2=[]
for entry in manifest2['files']:
 src=Path(entry['path']);dst=seed2/src.name
 assert hashlib.sha256(src.read_bytes()).hexdigest()==entry['sha256'],str(src)
 if not dst.exists():shutil.copyfile(src,dst)
 assert hashlib.sha256(dst.read_bytes()).hexdigest()==entry['sha256'],str(dst)
 records2.append(dict(path=str(dst),sha256=entry['sha256'],bytes=dst.stat().st_size))
(b/'NJX_NJO_SEED.json').write_text(json.dumps(dict(files=records2,total_bytes=sum(z['bytes'] for z in records2))))



p=b/{(a+'.json')!r};x=json.loads(p.read_text());roots=x.get('env',{{}}).get('LEAN_PATH','').split(':');rels=set();pins={{}}
if x['kind'] in ['lean','audit']:
 for root in roots:
  for stem in ['Aeneas','AeneasMeta']:
   q=Path(root)/stem
   if q.is_dir():rels.update(str(z.relative_to(root)) for z in q.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
   if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
 if x['kind']=='lean':
  for n in re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M):rels.add(n.replace('.','/')+'.olean')
 else:
  modules=list(json.loads((b/'NJX_GATE_SOURCES.json').read_text())['passed'])+['NJX_COMBINED_IMPORT','NIU_COMBINED_IMPORT','NGK_COMBINED_IMPORT','NFA_WALKER','NFA_MemoryLimit']
  for n in modules:rels.add(n.replace('.','/')+'.olean')
 for rel in sorted(rels):
  q=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert q is not None,rel
  for z in [q,Path(str(q)+'.private'),Path(str(q)+'.server'),q.with_suffix('.ir')]:
   if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
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
with (E/'NJX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
