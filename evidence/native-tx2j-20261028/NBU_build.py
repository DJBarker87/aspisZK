"""Own serial transport wrapper; invokes byte-identical S2H/S2W backends.
Batches transfer/recovery to avoid repeated flaky connections. No backend edits.
"""
from pathlib import Path
import subprocess,sys,json,time,shlex,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2j-20261028';C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,local,module=sys.argv[1:];local=Path(local);src='NBU_generated/'+module.replace('.','/')+'.lean';obj='/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028/'+module.replace('.','/')+'.olean'
if (E/'NBU_PAUSE').exists():raise SystemExit('paused before admission')
assert len(list(E.glob('NBU_L*/receipt.json')))<120
assert not (E/a/'receipt.json').exists()
def ssh(code,submitted=False):
 argv=['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code]
 for n in range(11):
  r=subprocess.run(argv,capture_output=True,text=True)
  with (E/'NBU_STEP_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,trial=n,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,submitted=submitted,argv=argv))+'\n')
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
cfg=dict(attempt=a,kind='lean',module=module,sources=[src],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NBU_generated','-o',obj,src],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'LEAN_PATH':'/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028:'+C+':'+C+'/objects:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'},deps_fingerprint={'scope':'Private prefix modules; persistent leaf cache and coherent SInt2; Aeneas objects pinned in NBU_LIBRARY_PIN.json'},expected_time='single module symbolic elaboration',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
q=E/a/'sources'/src;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(local.read_bytes())
payload=dict(cfg=cfg,source=local.read_text(),src=src,obj=obj,launchers=json.loads((E/'NBU_LAUNCHER_INPUTS.json').read_text()))
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
c=Path({C!r})/'objects';paths=[c/'Aeneas.olean']+list((c/'Aeneas').rglob('*.olean'))
pins={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in paths}}
p=b/'NBU_LIBRARY_PIN.json'
if p.exists(): assert json.loads(p.read_text())==pins,'library pin changed'
else:p.write_text(json.dumps(pins,indent=2)+'\\n')
'''
# Submission is never retried, including transport failures; recover read-only.
cmd='cd '+shlex.quote(B)+' && python3 -c '+shlex.quote(setup)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py '+shlex.quote(a+'.json')
r=ssh(cmd,submitted=True);(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
recover=f'''from pathlib import Path
import json
b=Path({B!r});names=[{(a+'/receipt.json')!r},{(a+'/stdout.log')!r},{(a+'/time.log')!r},'NBU_LIBRARY_PIN.json']
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).is_file()}}))
'''
r=ssh('python3 -c '+shlex.quote(recover));assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
if a+'/receipt.json' not in out:raise SystemExit('STOP no prover receipt; inspect setup/launcher, do not resubmit blindly')
rc=json.loads(out[a+'/receipt.json']);print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-16000:])
