"""Own serial validation client for the unchanged SInt2 scope runner."""
from pathlib import Path
import subprocess,json,hashlib,shlex,sys,time,re
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-pc-pool-library1-cache-20261110'
H='dombarker@100.108.41.90'; T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,plan_name=sys.argv[1:];assert re.fullmatch(r'PCM_E\d{3}',a)
assert not (E/a).exists()
assert len(list(E.glob('PCM_E[0-9][0-9][0-9]/receipt.json')))<10

def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
  with (E/'PCM_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,event='transport',retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted: recover read-only; do not resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')

# Six scopes is a separate admission condition in addition to the reservation JSON.
for share_retry in range(11):
 r=ssh('python3',"""import pathlib,subprocess,json
lines=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--no-pager'],text=True).splitlines(); units=[]
for line in lines:
 u=line.split()[0]; cg=subprocess.check_output(['systemctl','--user','show',u,'-p','ControlGroup','--value'],text=True).strip()
 try:pids=pathlib.Path('/sys/fs/cgroup'+cg+'/cgroup.procs').read_text().split()
 except FileNotFoundError:continue
 for pid in pids:
  try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True))
  except (FileNotFoundError,PermissionError,ProcessLookupError):continue
  if cwd.startswith('/home/dombarker/project-offloads/codex-'):units.append(u);break
print(json.dumps(dict(count=len(units),units=units)))
""")
 assert r.returncode==0,r.stderr
 share=json.loads(r.stdout)
 with (E/'PCM_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,event='scope_share',reply=share))+'\n')
 if share['count']<6:break
 if share_retry==10:raise RuntimeError('Host share refused after ten waits')
 time.sleep(180)

for retry in range(7):
 r=ssh('python3',f'import shutil,json;print(json.dumps(shutil.disk_usage({B!r})._asdict()))')
 assert r.returncode==0,r.stderr
 d=json.loads(r.stdout);(E/(a+'-disk-'+str(retry)+'.json')).write_text(r.stdout)
 if d['free']>=40_000_000_000:break
 if retry==6:raise RuntimeError('Disk exhausted after six ten-minute waits')
 time.sleep(600)
for retry in range(11):
 r=ssh('python3',f'''import subprocess,pathlib,json,sys
b=pathlib.Path({B!r});p=b/{(a+'-admission.json')!r}
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+'-barrier-'+str(retry)+'.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP shared admission missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  print('PCM admission refusal; waiting',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP shared admission failure')
plan=json.loads((E/plan_name).read_text());assert plan['attempt']==a
names=['PCM_extract_body.py',plan_name,'PCM_EXTRACT_INPUTS.json.xz','PCM_EXTRACT_SOURCE_MANIFEST.json','PCM_NCO_TOOL_PINS.json']
import base64,lzma
encoded={n:base64.b64encode((E/n).read_bytes()).decode() for n in names}
config=dict(attempt=a,kind='extraction',module=plan.get('label',str(plan.get('roots'))),sources=names,command=['python3','PCM_extract_body.py',plan_name],env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/PCM_tmp'),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=dict(frozen_source_manifest_sha256=hashlib.sha256((E/'PCM_EXTRACT_SOURCE_MANIFEST.json').read_bytes()).hexdigest(),NCO_pins_sha256=hashlib.sha256((E/'PCM_NCO_TOOL_PINS.json').read_bytes()).hexdigest()),expected_time='Optimized frozen Rust dependency/MIR compilation' if plan['phase'] in ['charon','both'] else 'Pinned Aeneas route emission; no proof')
encoded[a+'.json']=base64.b64encode(json.dumps(config).encode()).decode()
r=ssh('python3',f"""from pathlib import Path
import base64,json
b=Path({B!r});files=json.loads({json.dumps(encoded)!r})
for n,s in files.items():(b/n).write_bytes(base64.b64decode(s))
""");assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f"""from pathlib import Path
import json,base64,lzma,hashlib
b=Path({B!r});a={a!r};ps=list((b/a).rglob('*'))+[q for p in b.glob(a+'_*') for q in (p.rglob('*') if p.is_dir() else [p])]+[b/(a+'.llbc')];out={{}}
for p in ps:
 if not p.is_file():continue
 n=str(p.relative_to(b));raw=p.read_bytes()
 if len(raw)>20_000_000:
  out[n+'.sha256']=base64.b64encode((hashlib.sha256(raw).hexdigest()+'\\n').encode()).decode()
  out[n+'.xz']=base64.b64encode(lzma.compress(raw,preset=6)).decode()
 else:out[n]=base64.b64encode(raw).decode()
print(json.dumps(out))
""");assert r.returncode==0,r.stderr
for n,value in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(value))
rc=json.loads((E/a/'receipt.json').read_text())
with (E/'PCM_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps']}))
sys.exit(rc['exit_status'])
