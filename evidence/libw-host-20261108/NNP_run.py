"""Private serial validation client; invokes the unchanged S2W host runner."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,re
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-libw-host-20261108'
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,target=sys.argv[1:]; assert re.fullmatch('NNP_L[0-9]{3}',a)
def record(x):
 with (E/'NNP_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,**x))+'\n')
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  if r.returncode!=255:return r
  record(dict(event='transport_wait',retry=retry,submitted=submitted,stderr=r.stderr))
  if submitted:raise RuntimeError('Submitted: recover read-only; never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
used={json.loads(l)['attempt'] for l in (E/'NNP_ATTEMPTS.jsonl').read_text().splitlines() if json.loads(l).get('event')=='submitted'} if (E/'NNP_ATTEMPTS.jsonl').exists() else set()
assert len(used)<16 and a not in used
while True:
 r=ssh('python3', '''import subprocess,pathlib,json
found=[]
for line in subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--no-pager'],text=True).splitlines():
 unit=line.split()[0];cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip()
 try:pids=pathlib.Path('/sys/fs/cgroup'+cg+'/cgroup.procs').read_text().split()
 except FileNotFoundError:continue
 for pid in pids:
  try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True))
  except (FileNotFoundError,PermissionError,ProcessLookupError):continue
  if cwd.startswith('/home/dombarker/project-offloads/codex-'):found.append(unit);break
print(json.dumps(dict(scopes=found,count=len(found))))
''');assert r.returncode==0,r.stderr
 share=json.loads(r.stdout);record(dict(event='share_check' if share['count']<6 else 'wait',host=share))
 if share['count']<6:break
 time.sleep(180)
for retry in range(7):
 r=ssh('python3',f'import shutil,json;print(json.dumps(shutil.disk_usage({B!r})._asdict()))');assert r.returncode==0,r.stderr
 disk=json.loads(r.stdout);record(dict(event='disk_check',disk=disk));
 if disk['free']>=40_000_000_000:break
 if retry==6:raise RuntimeError('Disk below40GB after six waits')
 record(dict(event='wait',reason='disk below40GB'));time.sleep(600)
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r})
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r};print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:record(dict(event='wait',reason='missing admission'));time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  record(dict(event='wait',reason='reservation refused',exit=r.returncode,reservation=ad));time.sleep(180);continue
 raise RuntimeError('STOP admission')
source=(E/(target+'.lean')) if target.startswith('NNP_') else E.parent/'libw-20261108'/(target+'.lean')
files={'NNP_generated/'+target+'.lean':source.read_text()}
LP=json.loads((E.parent/'libb-20261111/LIBB_L344.json').read_text())['env']['LEAN_PATH']
LP=LP.replace('/home/dombarker/project-offloads/codex-cx-libb-20261111/LIBB_objects',B+'/NNP_seedLIBB')
cfg=dict(attempt=a,kind='lean',module=target,sources=list(files),command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNP_generated','-o','NNP_objects/'+target+'.olean',next(iter(files))],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NNP_tmp',LEAN_PATH=B+'/NNP_objects:'+LP),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),deps_fingerprint={})
files[a+'.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil,re
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for d in ['NNP_generated','NNP_objects','NNP_tmp']: (b/d).mkdir(exist_ok=True)
if not (b/'NNP_seedLIBB').exists():shutil.copytree('/home/dombarker/project-offloads/codex-cx-libb-20261111/LIBB_objects',b/'NNP_seedLIBB')
for n in ['S2W_run_host.py','S2W_lean_host.py']:
 if not (b/n).exists():shutil.copy2('/home/dombarker/project-offloads/codex-cx-libb-20261111/'+n,b/n)
(b/'lakefile.toml').write_text('name = "nnp"\\nversion = "0.1.0"\\n');(b/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\\n')
for n,t in files.items():(b/n).write_text(t)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
rels=set()
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
rels.update(n.replace('.','/')+'.olean' for n in re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M))
for rel in sorted(rels):
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 assert p is not None,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins,'lean_binary_sha256':hashlib.sha256(Path({(T+'/bin/lean')!r}).read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
record(dict(event='submitted',target=target))
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});p=b/{a!r};files={{str(z.relative_to(b)):z.read_text() for z in p.rglob('*') if z.is_file()}}
z=b/'NNP_objects'/{(target+'.olean')!r}
files[{(a+'/object.json')!r}]=json.dumps(dict(path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size)) if z.exists() else 'null'
print(json.dumps(files))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(exist_ok=True,parents=True);p.write_text(t)
receipt=json.loads((E/a/'receipt.json').read_text());record(dict(event='complete',target=target,exit_status=receipt['exit_status']))
print(json.dumps({k:receipt[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
print((E/a/'stdout.log').read_text()[-5000:])
sys.exit(receipt['exit_status'])
