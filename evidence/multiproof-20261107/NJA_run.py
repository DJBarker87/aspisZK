"""Serial owned client; shared reservation and S2W launcher are unchanged."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,lzma,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-multiproof-20261107'
a=sys.argv[1];cfg=json.loads((E/(a+'.json')).read_text());assert cfg['attempt']==a
assert not (E/a).exists()
cfg['configuration_source_revision']=cfg.get('source_revision')
cfg['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=E,text=True).strip()
cfg['source_tree_dirty']=bool(subprocess.check_output(['git','status','--porcelain'],cwd=E,text=True).strip())
def ssh(code,data=None,submitted=False):
 for n in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
  with (E/'NJA_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=n,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted: recover read-only; never resubmit')
  if n<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for n in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/{(a+'-reservation.json')!r}
with (b/{(a+'-barrier-'+str(n)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{n}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if n==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad),indent=2)+'\n')
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and n<10:
  print('reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP admission')
# Upload only owned configuration / source inputs, after admission.
files={a+'.json':base64.b64encode(json.dumps(cfg).encode()).decode()}
for name in cfg.pop('upload',[]):files[name]=base64.b64encode((E/name).read_bytes()).decode()
r=ssh('python3',f'''from pathlib import Path
import json,shutil,base64
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(t))
p=b/'S2W_run_host.py'
if not p.exists():shutil.copy2('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S2W_run_host.py',p)
''');assert r.returncode==0,r.stderr
if cfg['kind']=='lean':
 r=ssh('python3',f'''from pathlib import Path
import json,re,hashlib,shutil
b=Path({B!r});p=b/{(a+'.json')!r};x=json.loads(p.read_text());roots=x['env']['LEAN_PATH'].split(':')
if '-o' in x['command']:(b/x['command'][x['command'].index('-o')+1]).parent.mkdir(parents=True,exist_ok=True)
(b/'NJA_objects').mkdir(exist_ok=True);(b/'lakefile.lean').write_text('import Lake\\nopen Lake DSL\\npackage nhr\\n')
pins={{}};rels=set()
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  path=Path(root)/stem
  if path.is_dir():rels.update(str(z.relative_to(root)) for z in path.rglob('*') if z.is_file() and str(z).endswith(('.olean','.olean.private','.olean.server','.ir')))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
for name in x['sources']:
 if name.endswith('.lean'):
  rels.update(m.replace('.','/')+'.olean' for m in re.findall(r'^import ([A-Za-z0-9_.]+)',(b/name).read_text(),re.M))
for rel in sorted(rels):
 z=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert z is not None,rel
 for q in [z,Path(str(z)+'.private'),Path(str(z)+'.server'),z.with_suffix('.ir')]:
  if q.is_file():pins[str(q)]={{'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins}};p.write_text(json.dumps(x,indent=2))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list((b/{a!r}).rglob('*'))
for n in {cfg.get('collect',[])!r}:
 p=b/n;paths+=list(p.rglob('*')) if p.is_dir() else [p]
print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in paths if p.is_file()}}))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);raw=t.encode()
 if len(raw)>1000000:
  p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:p.write_bytes(raw)
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k not in ['deps_fingerprint','env']}
entry['full_receipt']=a+'/receipt.json'
with (E/'NJA_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
