"""Serial owned client; shared reservation and S2W launcher are unchanged."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,lzma,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-poseidon-state-20261108'
a=sys.argv[1];cfg=json.loads((E/(a+'.json')).read_text());assert cfg['attempt']==a
assert not cfg.get('cancelled'),cfg.get('cancelled')
assert not (E/a).exists()
history=[json.loads(line) for line in (E/'NKG_ATTEMPTS.jsonl').read_text().splitlines() if line.strip()]
assert cfg['kind'] in ('lean','link','audit','kani'), 'No extraction or unbudgeted proof kind admitted'
if cfg['kind']=='kani':assert sum(x['kind']=='kani' for x in history)<80,'Kani budget exhausted'
else:assert sum(x['kind'] in ('lean','link','audit') for x in history)<90,'Lean/link/audit budget exhausted'
cfg['configuration_source_revision']=cfg.get('source_revision')
cfg['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=E,text=True).strip()
cfg['source_tree_dirty']=bool(subprocess.check_output(['git','status','--porcelain'],cwd=E,text=True).strip())
def ssh(code,data=None,submitted=False):
 for n in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
  with (E/'NKG_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=n,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
if '-c' in x['command']:(b/x['command'][x['command'].index('-c')+1]).parent.mkdir(parents=True,exist_ok=True)
(b/'NKG_objects').mkdir(exist_ok=True);(b/'lakefile.lean').write_text('import Lake\\nopen Lake DSL\\npackage nhr\\n')
pins={{}};rels=set()
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  path=Path(root)/stem
  if path.is_dir():rels.update(str(z.relative_to(root)) for z in path.rglob('*') if z.is_file() and str(z).endswith(('.olean','.olean.private','.olean.server','.ir')))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
for name in x['sources']:
 if name.endswith('.lean'):
  rels.update(m.replace('.','/')+'.olean' for m in re.findall(r'^import (?:all )?([A-Za-z0-9_.]+)',(b/name).read_text(),re.M))
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
with (E/'NKG_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));
if cfg['kind']=='kani':
 log_path=E/a/'stdout.log'
 if log_path.exists(): semantic_log=log_path.read_text()
 else:
  import lzma
  semantic_log=lzma.open(str(log_path)+'.xz').read().decode()
 if any(term in semantic_log.lower() for term in ['cbmc timed out','timed out','time limit exceeded']):
  print('NKG review: TIMEOUT gives no positive or control credit '+a);sys.exit(2)
 if rc['exit_status']==1 and 'VERIFICATION:- FAILED' not in semantic_log and 'VERIFICATION FAILED' not in semantic_log:
  print('NKG review: no semantic failing-control verdict '+a);sys.exit(2)
if cfg['kind']=='kani' and rc['exit_status'] in (0,1):
 expected_fail=cfg.get('expected_failure', 'NKG_bad_argument' in cfg.get('env',{}).get('RUSTFLAGS',''))
 if (rc['exit_status']==1)!=expected_fail: print('NKG review: unexpected semantic verdict '+a);sys.exit(2)
sys.exit(rc['exit_status'])
