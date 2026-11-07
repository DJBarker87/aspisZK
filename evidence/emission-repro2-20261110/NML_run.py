"""Serial owned client; shared reservation and S2W launcher are unchanged."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,lzma,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-emission-repro2-20261110'
a=sys.argv[1];cfg=json.loads((E/(a+'.json')).read_text());assert cfg['attempt']==a
assert not (E/a).exists()
cfg['configuration_source_revision']=cfg.get('source_revision')
cfg['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=E,text=True).strip()
cfg['source_tree_dirty']=bool(subprocess.check_output(['git','status','--porcelain'],cwd=E,text=True).strip())
def ssh(code,data=None,submitted=False):
 for n in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
  with (E/'NML_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=n,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted: recover read-only; never resubmit')
  if n<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
# Read-only share gate; every refusal is recorded as a wait, never a launch.
def share_gate():
 while True:
  r=ssh('python3',(E/'NML_share.py').read_text());assert r.returncode==0,r.stderr
  x=json.loads(r.stdout)
  with (E/'NML_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,kind='share_check' if x['stream_a_count']<2 else 'wait',reason='Stream A scope gate',observation=x))+'\n')
  if x['stream_a_count']<2:return x
  print(json.dumps(dict(attempt=a,wait='Stream A scopes',count=x['stream_a_count'])),flush=True);time.sleep(180)
share_gate()
# Disk admission before EVERY scope; no compiler runs here.
for disk_retry in range(7):
 r=ssh('python3',f"import shutil,json,os;root={B!r};print(json.dumps(dict(free=shutil.disk_usage(root.rsplit('/',1)[0]).free,owned_bytes=sum(os.stat(os.path.join(d,n)).st_size for d,ds,ns in os.walk(root) for n in ns))))")
 assert r.returncode==0,r.stderr
 disk=json.loads(r.stdout);(E/(a+f'-disk-{disk_retry}.json')).write_text(json.dumps(disk)+'\n')
 assert disk['owned_bytes']<30_000_000_000, 'STOP owned host writes exceed 30 GB'
 if disk['free']>=40_000_000_000:break
 if disk_retry==6:raise RuntimeError('STOP host disk below 40 GB')
 time.sleep(600)
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
(b/'NML_objects').mkdir(exist_ok=True);(b/'lakefile.lean').write_text('import Lake\\nopen Lake DSL\\npackage nhr\\n')
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
share_gate()
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r})
import hashlib
manifest=json.loads((b/'NML_STAGING_MANIFEST.json').read_text());w=b/'NML_workspace'
changed=[n for n,v in manifest['files'].items() if not (w/n).is_file() or hashlib.sha256((w/n).read_bytes()).hexdigest()!=v['sha256']]
post=dict(attempt={a!r},source_drift=changed,lock_sha256=hashlib.sha256((w/'Cargo.lock').read_bytes()).hexdigest(),expected_lock_sha256=manifest['files']['Cargo.lock']['sha256'],owned_bytes=sum(p.stat().st_size for p in b.rglob('*') if p.is_file()),axioms='not applicable: extraction only')
(b/{a!r}/'NML_POSTCHECK.json').write_text(json.dumps(post,indent=2))
assert not changed and post['lock_sha256']==post['expected_lock_sha256'],'STOP frozen source/lock drift'
assert post['owned_bytes']<30_000_000_000,'STOP owned disk exceeds 30 GB'
paths=list((b/{a!r}).rglob('*'))
for n in {cfg.get('collect',[])!r}:
 p=b/n;paths+=list(p.rglob('*')) if p.is_dir() else [p]
print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in paths if p.is_file() and p.suffix != '.llbc' and p.name not in ['metadata.json','metadata.stdout']}}))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);raw=t.encode()
 if len(raw)>1000000:
  p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:p.write_bytes(raw)
r=ssh('python3',f"from pathlib import Path;import json,base64,lzma,hashlib;b=Path({B!r});print(json.dumps({{str(p.relative_to(b)):dict(data=base64.b64encode(lzma.compress(p.read_bytes(),preset=6)).decode(),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in (b/( {a!r}+'_emitted')).glob('*.llbc')}}))")
assert r.returncode==0,r.stderr
for n,d in json.loads(r.stdout).items():
 p=E/n;p.with_name(p.name+'.xz').write_bytes(base64.b64decode(d['data']));p.with_name(p.name+'.sha256').write_text(d['sha256']+'\n')
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k not in ['deps_fingerprint','env']}
entry['full_receipt']=a+'/receipt.json'
with (E/'NML_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
