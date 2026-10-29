"""Lane-owned inputs and transport; the capped host runner is unchanged."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-leaves-20261029';H='dombarker@100.108.41.90';C='/home/dombarker/project-offloads/codex-cx-slice-s-leaves-cache-20261029';S='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,kind,target=sys.argv[1:];prior=[json.loads(l) for l in (E/'NEC_ATTEMPTS.jsonl').read_text().splitlines() if l]
assert sum(r['kind']==kind for r in prior)<dict(lean=80,kani=80,extract=20)[kind]
assert not (E/a).exists()
def remote(code,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
  with (E/'NEC_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,submitted=submitted,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('transport exhausted')
for retry in range(11):
 r=remote(f'''import pathlib,subprocess,sys
b=pathlib.Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP infrastructure: reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('reservation wait',flush=True);time.sleep(180);continue
 raise SystemExit('STOP infrastructure admission')
files={}
if kind=='lean':
 files['NEC_generated/'+target+'.lean']=(E/(target+'.lean')).read_text()
 cmd=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NEC_generated','-o','NEC_objects/'+target+'.olean','NEC_generated/'+target+'.lean']
else:raise ValueError('native/extraction config not installed yet')
cfg=dict(attempt=a,kind=kind,module=target,sources=list(files),command=cmd,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',LEAN_PATH=B+'/NEC_objects:'+C+'/NDM_front4b_objects_20261029:'+C+':'+S+':'+S+'/objects'),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={})
files[a+'.json']=json.dumps(cfg)
(E/a/'sources').mkdir(parents=True)
for n,s in files.items():
 p=E/a/'sources'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
r=remote(f'''from pathlib import Path
import json,hashlib
b=Path({B!r})
for n,s in {files!r}.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
p=b/{(a+'.json')!r};cfg=json.loads(p.read_text());pins=json.loads((b/'NEC_OBJECT_PINS.json').read_text())
for q in (b/'NEC_objects').rglob('*.olean'):pins[str(q)]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest())
cfg['deps_fingerprint']['selected_objects']=pins
p.write_text(json.dumps(cfg,indent=1))
''');assert r.returncode==0,r.stdout+r.stderr
r=remote(f'''import subprocess,sys
r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','S2W_run_host.py',{(a+'.json')!r}],cwd={B!r})
sys.exit(r.returncode)
''',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=remote(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log']!r} if (b/n).exists()}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'missing receipt; recover read-only, never resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NEC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-2400:])
