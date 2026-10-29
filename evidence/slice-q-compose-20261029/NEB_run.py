#!/usr/bin/env python3
"""Serial lane-owned Lean validation driver; unchanged S2W host runner."""
from pathlib import Path
import hashlib,json,subprocess,sys,time,shlex
E=Path(__file__).resolve().parent;R=E.parent.parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-q-compose-20261029'
CACHE='/home/dombarker/project-offloads/codex-cx-slice-q-compose-cache-20261029'
COHERENT='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,module=sys.argv[1:];assert a.startswith('NEB_L') and 1<=int(a[-3:])<=150
assert module.startswith('NEB_') and not (E/a).exists()
active=E/'NEB_ACTIVE.json';assert not active.exists();active.write_text(json.dumps(dict(attempt=a,module=module)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NEB_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('transport exhausted')
for retry in range(11):
 code=f'''import pathlib,subprocess,json,sys
b=pathlib.Path({B!r});log=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with log.open('w') as f:r=subprocess.run(['python3',{COHERENT!r}+'/JFz_reservation.py',str(b/{(a+'-admission.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(log.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP infrastructure: missing admission JSON')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit_status=r.returncode,reservation=ad),indent=1)+'\n')
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  print('reservation refused; wait three minutes',flush=True);time.sleep(180);continue
 raise SystemExit('STOP infrastructure admission')
source=(E/(module+'.lean')).read_text()
# Pin the exact direct objects, plus every Aeneas library object in the resolved
# coherent path; imported-cache hashes are independently recorded at intake.
code=f'''from pathlib import Path
import json,hashlib
roots={[B,CACHE,COHERENT,COHERENT+'/objects']!r};src={source!r};seen={{}}
for line in src.splitlines():
 if line.startswith('import '):
  for mod in line[7:].split():
   key=mod.replace('.','/')+'.olean'
   p=next((Path(root)/key for root in roots if (Path(root)/key).is_file()),None)
   if p is None:raise FileNotFoundError(mod)
   seen[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
for p in Path({COHERENT!r}+'/objects').rglob('*.olean*'):
 if p.relative_to(Path({COHERENT!r}+'/objects')).parts[0].split('.')[0]=='Aeneas':
  seen[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
print(json.dumps(seen))
'''
r=ssh('python3',code);assert r.returncode==0,r.stdout+r.stderr
pins=json.loads(r.stdout)
cfg=dict(attempt=a,kind='lean',module=module,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,sources=[module+'.lean'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o',module+'.olean',module+'.lean'],timeout=180,env=dict(LEAN_PATH=':'.join([B,CACHE,COHERENT,COHERENT+'/objects'])),deps_fingerprint=dict(selected_objects=pins,cache_import_manifest_sha256=hashlib.sha256((E/'NEB_CACHE_IMPORTS.json').read_bytes()).hexdigest()),expected_time='Focused symbolic call-domain proof; no native multiplication or recurrence evaluation')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
files={module+'.lean':source,a+'.json':json.dumps(cfg)}
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r})
for n,s in json.loads({json.dumps(files)!r}).items():(b/n).write_text(s)
(b/'lakefile.toml').write_text('name = "neb"\\nversion = "0.1.0"\\n')
(b/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\\n')
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
# Submission is never retried, including after transport failure.
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'/sources/'+module+'.lean']!r}
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).exists()}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'unresolved submitted attempt: recover read-only, never resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NEB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
active.unlink()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
print(out[a+'/stdout.log'][-3500:],flush=True)
sys.exit(rc['exit_status'])
