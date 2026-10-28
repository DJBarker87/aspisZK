"""Own serial transport wrapper; invokes byte-identical S2H/S2W backends.
Batches transfer/recovery to avoid repeated flaky connections. No backend edits.
"""
from pathlib import Path
import subprocess,sys,json,time,shlex,hashlib,zlib,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2j-20261028';C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,local,module=sys.argv[1:];local=Path(local);src='NCC_generated/'+module.replace('.','/')+'.lean';obj='/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028/'+module.replace('.','/')+'.olean'
if (E/'NCC_PAUSE').exists():raise SystemExit('paused before admission')
assert len(list(E.glob('NCC_L*/receipt.json')))<60
assert not (E/a/'receipt.json').exists()
def ssh(code,submitted=False):
 argv=['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code]
 for n in range(11):
  try:r=subprocess.run(argv,capture_output=True,text=True,timeout=None if submitted else 90)
  except subprocess.TimeoutExpired:
   with (E/'NCC_STEP_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,trial=n,actual_exit=None,transport_timeout_seconds=90,submitted=submitted,argv=argv))+'\n')
   if n<10:time.sleep(60);continue
   raise SystemExit('STOP prelaunch/read-only transport timeout exhausted')
  with (E/'NCC_STEP_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,trial=n,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,submitted=submitted,argv=argv))+'\n')
  if r.returncode!=255 or submitted:return r
  if n<10:print('prelaunch/read-only transport retry60s',flush=True);time.sleep(60)
 raise SystemExit('STOP transport exhausted')
for retry in range(11):
 script=f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text(),end='');sys.exit(r.returncode)
'''
 r=ssh('python3 -c '+shlex.quote(script));(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP admission JSON missing '+r.stdout+r.stderr)
 (E/(a+'-reservation.json')).write_text(json.dumps(ad,indent=2)+'\n')
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('admission refused; wait180s',flush=True);time.sleep(180);continue
 raise SystemExit('STOP admission error')
else:raise SystemExit('STOP admission exhausted')
# Own validation repair: pin the actual first-resolved direct import objects.
import re
imports=re.findall(r'^import (\S+)',local.read_text(),re.M)
pin_code=f"""from pathlib import Path
import hashlib,json
roots=[Path('/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028'),Path({C!r}),Path({(C+'/objects')!r})]
pins={{}}
for name in {imports!r}:
 rel=name.replace('.','/')+'.olean';p=next((r/rel for r in roots if (r/rel).is_file()),None)
 assert p is not None,('missing import',name)
 pins[name]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
print(json.dumps(pins,sort_keys=True))
"""
pin_run=ssh('python3 -c '+shlex.quote(pin_code));assert pin_run.returncode==0,pin_run.stdout+pin_run.stderr
import_pins=json.loads(pin_run.stdout)
(E/(a+'-imports.json')).write_text(json.dumps(import_pins,indent=2)+'\n')
cfg=dict(attempt=a,kind='lean',module=module,sources=[src],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NCC_generated','-o',obj,src],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'LEAN_PATH':'/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028:'+C+':'+C+'/objects:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'},deps_fingerprint={'sha256':hashlib.sha256(json.dumps(import_pins,sort_keys=True).encode()).hexdigest(),'direct_imports':import_pins,'Aeneas':'NCC_LIBRARY_PIN.json','private_dependency_journal_sha256':hashlib.sha256((E/'NCC_DEPENDENCY_ATTEMPTS.jsonl').read_bytes()).hexdigest() if (E/'NCC_DEPENDENCY_ATTEMPTS.jsonl').exists() else None},expected_time='single module symbolic elaboration',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
q=E/a/'sources'/src;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(local.read_bytes())
payload=dict(cfg=cfg,source=local.read_text(),src=src,obj=obj,launchers=json.loads((E/'NCC_LAUNCHER_INPUTS.json').read_text()))
# Data serialization is shell-quoted; input source is never shell code.
setup=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});x=json.loads({json.dumps(json.dumps(payload))})
for n in ['S2W_lean_host.py','S2W_run_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:
 p=b/n;s=x['launchers'][n]
 if p.exists():assert p.read_text()==s,(n,'unchanged backend mismatch')
 else:p.write_text(s)
for n in [x['src'],x['obj']]: (b/n).parent.mkdir(parents=True,exist_ok=True)
(b/x['src']).write_text(x['source']);(b/{(a+'.json')!r}).write_text(json.dumps(x['cfg'],indent=2)+'\\n')
roots=[Path('/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028'),Path({C!r}),Path({(C+'/objects')!r}),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
names={{'Aeneas.olean'}}
for root in roots:
 names.update(str(p.relative_to(root)) for p in (root/'Aeneas').rglob('*.olean'))
paths=[next(root/name for root in roots if (root/name).is_file()) for name in sorted(names)]
pins={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in paths}}
p=b/'NCC_LIBRARY_PIN.json'
if p.exists(): assert json.loads(p.read_text())==pins,'library pin changed'
else:p.write_text(json.dumps(pins,indent=2)+'\\n')
'''
# Own transport repair: complete setup before the one small detached submission.
encoded=base64.b64encode(zlib.compress(setup.encode(),9)).decode()
r=ssh('python3 -c '+shlex.quote('import base64,zlib;exec(zlib.decompress(base64.b64decode('+repr(encoded)+')))'))
assert r.returncode==0,r.stdout+r.stderr
cmd='cd '+shlex.quote(B)+' && nohup systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py '+shlex.quote(a+'.json')+' > '+shlex.quote(a+'-host-launcher.log')+' 2>&1 < /dev/null &'
r=ssh(cmd,submitted=True);(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
recover=f'''from pathlib import Path
import json,zlib,base64
b=Path({B!r});names=[{(a+'/receipt.json')!r},{(a+'/stdout.log')!r},{(a+'/time.log')!r},{(a+'-host-launcher.log')!r},'NCC_LIBRARY_PIN.json']
x={{n:(b/n).read_text() for n in names if (b/n).is_file()}}
print(base64.b64encode(zlib.compress(json.dumps(x).encode(),9)).decode())
'''
for recovery in range(22):
 r=ssh('python3 -c '+shlex.quote(recover));assert r.returncode==0,r.stderr
 out=json.loads(zlib.decompress(base64.b64decode(r.stdout)))
 for n,data in out.items():q=E/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(data)
 if a+'/receipt.json' in out:break
 time.sleep(10)
else:raise SystemExit('STOP unresolved submission; never resubmit unchanged')
rc=json.loads(out[a+'/receipt.json'])
with (E/'NCC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-20000:])
