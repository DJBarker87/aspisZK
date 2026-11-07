"""NNG-owned input client; unchanged S2W launcher and admission infrastructure."""
from pathlib import Path
import json, subprocess, sys, time, hashlib, shlex, re, os, atexit
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-tx1-principal-20261111'
a=sys.argv[1]; assert re.fullmatch(r'NNG_[LKE][0-9]{3}',a)
x=json.loads((E/(a+'.json')).read_text()); assert x['attempt']==a
x.setdefault('env',{}).setdefault('CARGO_TARGET_DIR',B+'/NNG_target')
assert int(a[-3:])>=1
# Count actual scopes, including conservative unresolved submissions, not id gaps.
submitted=set()
for line in (E/'NNG_TRANSPORT.jsonl').read_text().splitlines():
 row=json.loads(line)
 if row.get('submitted'):submitted.add(row['attempt'])
completed={json.loads(line)['attempt'] for attempt_file in sorted(E.glob('NNG_ATTEMPTS*.jsonl')) for line in attempt_file.read_text().splitlines() if json.loads(line).get('kind')!='wait'}
assert a not in submitted, 'Never resubmit after any recorded submission; recover read-only'
def budget_group(kind):
 return 'lean_link_audit' if kind in ['lean','link','audit'] else ('kani' if kind=='kani' else ('extract' if kind=='extract' else None))
used={'lean_link_audit':set(),'kani':set(),'extract':set()}
for attempt in completed|submitted:
 config=E/(attempt+'.json')
 assert config.exists(), 'Missing submitted-attempt budget configuration: '+attempt
 group=budget_group(json.loads(config.read_text())['kind'])
 if group:used[group].add(attempt)
limits={'lean_link_audit':509,'kani':10,'extract':2};group=budget_group(x['kind'])
if group:assert len(used[group])<limits[group], 'Actual scope budget exhausted: '+group
with (E/'NNG_BUDGET_ADMISSIONS.jsonl').open('a') as out:out.write(json.dumps({'attempt':a,'kind':x['kind'],'used':{g:len(s)for g,s in used.items()},'limits':limits,'unresolved_submissions':sorted(submitted-completed)})+'\n')
if x['command'][:2]==['python3','NNG_gate.py']:assert x['command'][2]==a+'.json','Stale gate configuration'
assert not (E/a/'receipt.json').exists(), 'Never resubmit'
if x['kind']=='kani':assert x['sources']==['NNG_gate.py','NNG_SOURCE_PINS.json','NNG_FROZEN_FILE_PINS.json','NNG_BASE_EXPECTED.json'] or (x['command'][:2]==['python3','NNG_gate_pair.py'] and x['sources']==['NNG_gate.py','NNG_gate_pair.py','NNG_SOURCE_PINS.json','NNG_FROZEN_FILE_PINS.json']),'Native inputs must be installed in a prior capped scope; never upload source snapshots'
guard=E/'NNG_CLIENT_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
  with (E/'NNG_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Recover read-only; never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for disk_retry in range(7):
 r=ssh('python3',"import shutil,json;print(json.dumps(shutil.disk_usage('/home/dombarker/project-offloads')._asdict()))")
 assert r.returncode==0,r.stderr
 info=json.loads(r.stdout);(E/(a+'-disk-'+str(disk_retry)+'.json')).write_text(json.dumps(info))
 if info['free']>=40_000_000_000:break
 if disk_retry==6:raise RuntimeError('STOP disk below40GB after six waits')
 for _ in range(10):time.sleep(60)
while True:
 r=ssh('python3',"""import subprocess,pathlib,os,json
out=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True)
scopes=[]
for line in out.splitlines():
 unit=line.split()[0]
 cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip()
 if not cg:continue
 hit=False
 for f in pathlib.Path('/sys/fs/cgroup'+cg).rglob('cgroup.procs'):
  for pid in f.read_text().split():
   try: cwd=os.readlink('/proc/'+pid+'/cwd')
   except OSError:continue
   if cwd.startswith('/home/dombarker/project-offloads/'):hit=True
 if hit:scopes.append(unit)
print(json.dumps({'scopes':scopes,'count':len(scopes)}))""")
 assert r.returncode==0,r.stderr
 share=json.loads(r.stdout)
 with (E/'NNG_SHARE.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,**share))+'\n')
 if share['count']<6:break
 with (E/'NNG_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,kind='wait',reason='whole-host saturation under bm',**share))+'\n')
 print('whole-host wait: '+str(share['count'])+' scopes',flush=True)
 for _ in range(3):time.sleep(60)
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
files={n:({'base64':__import__('base64').b64encode((E/n).read_bytes()).decode()} if n.endswith('.xz') else (E/n).read_text()) for n in x['sources'] if (E/n).is_file()}
files[a+'.json']=json.dumps(x)
r=ssh('python3',f'''from pathlib import Path
import json,shutil,hashlib,re
b=Path({B!r});w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 if not (b/n).exists():shutil.copyfile(w/n,b/n)
for n,t in json.loads({json.dumps(files)!r}).items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(__import__('base64').b64decode(t['base64'])) if isinstance(t,dict) else p.write_text(t)
for n in ['NNG_objects','NNG_generated','NNG_tmp','NNG_native']:(b/n).mkdir(exist_ok=True)
p=b/{(a+'.json')!r};x=json.loads(p.read_text());roots=x.get('env',{{}}).get('LEAN_PATH','').split(':');rels=set();pins={{}}
if x['kind']=='lean' and '-o' in x['command']:(b/x['command'][x['command'].index('-o')+1]).parent.mkdir(parents=True,exist_ok=True)
if x['kind'] in ['lean','audit','link']:
 for root in roots:
  for stem in ['Aeneas','AeneasMeta']:
   q=Path(root)/stem
   if q.is_dir():rels.update(str(z.relative_to(root)) for z in q.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
   if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
 for source in x['sources']:
  if source.endswith('.lean'):
   for n in re.findall(r'^import (?:all )?([\\w.]+)',(b/source).read_text(),re.M):rels.add(n.replace('.','/')+'.olean')
 if x['kind'] in ['audit','link']:
  for n in [x.get('audit_combined','NNG_COMBINED_IMPORT'),'NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations']+x.get('audit_modules',[]):rels.add(n.replace('.','/')+'.olean')
 for rel in sorted(rels):
  q=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert q is not None,rel
  for z in [q,Path(str(q)+'.private'),Path(str(q)+'.server'),q.with_suffix('.ir')]:
   if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins}};p.write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
# Fresh final admission: count/disk/reservation again immediately before submission.
final_failures=retry
final_missing=0
while True:
 r=ssh('python3',"import shutil,json;print(json.dumps({'free':shutil.disk_usage('/home/dombarker/project-offloads').free}))")
 assert r.returncode==0,r.stderr
 final_disk=json.loads(r.stdout)
 with (E/'NNG_FINAL_ADMISSION.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,kind='disk',**final_disk))+'\n')
 if final_disk['free']<40_000_000_000:
  final_disk_waits=locals().get('final_disk_waits',0)+1
  if final_disk_waits>6:raise RuntimeError('STOP final disk below40GB after six waits')
  with (E/'NNG_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,kind='wait',reason='final disk below40GB',**final_disk))+'\n')
  for _ in range(10):time.sleep(60)
  continue
 r=ssh('python3',"""import subprocess,pathlib,os,json
 out=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True)
 scopes=[]
 for line in out.splitlines():
  unit=line.split()[0]
  cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip()
  if not cg:continue
  hit=False
  for f in pathlib.Path('/sys/fs/cgroup'+cg).rglob('cgroup.procs'):
   for pid in f.read_text().split():
    try: cwd=os.readlink('/proc/'+pid+'/cwd')
    except OSError:continue
    if cwd.startswith('/home/dombarker/project-offloads/'):hit=True
  if hit:scopes.append(unit)
 print(json.dumps({'scopes':scopes,'count':len(scopes)}))""".replace("\n ","\n"))
 assert r.returncode==0,r.stderr
 final_share=json.loads(r.stdout)
 with (E/'NNG_FINAL_ADMISSION.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,kind='share',**final_share))+'\n')
 if final_share['count']>=6:
  with (E/'NNG_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,kind='wait',reason='final whole-host saturation under bm',**final_share))+'\n')
  print('Final whole-host wait: '+str(final_share['count'])+' scopes',flush=True)
  for _ in range(3):time.sleep(60)
  continue
 r=ssh('python3',f'''from pathlib import Path
 import subprocess,sys
 b=Path({B!r});b.mkdir(exist_ok=True)
 with (b/{(a+'-final-barrier-'+str(final_failures)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
 p=b/{(a+'-reservation.json')!r};print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
 '''.replace("\n ","\n"))
 (E/(a+'-final-barrier-'+str(final_failures)+'.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if final_missing==0:final_missing+=1;time.sleep(30);continue
  raise RuntimeError('STOP final missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and final_failures<10:
  final_failures+=1
  for _ in range(3):time.sleep(60)
  continue
 raise RuntimeError('STOP final admission')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=[str(p.relative_to(b)) for p in (b/{a!r}).rglob('*') if p.is_file()]+[{(a+'.json')!r}]+{x.get('collect',[])!r}
for pattern in {x.get('collect_globs',[])!r}:names += [str(p.relative_to(b)) for p in b.glob(pattern) if p.is_file()]
print(json.dumps({{n:({{'base64':__import__('base64').b64encode((b/n).read_bytes()).decode()}} if n.endswith('.xz') else (b/n).read_text()) for n in names if (b/n).is_file()}}))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if isinstance(t,dict):p.write_bytes(__import__("base64").b64decode(t["base64"]))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; recover, never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NNG_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
summary={k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']};summary['axiom_lines']=len(rc['print_axioms']) if isinstance(rc['print_axioms'],list) else 0;print(json.dumps(summary));sys.exit(rc['exit_status'])
