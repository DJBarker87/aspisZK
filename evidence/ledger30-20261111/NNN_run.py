"""Job-owned serial client of the unchanged S2W launcher and reservation barrier."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,re,os,atexit,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNN_20261111';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,kind,target=sys.argv[1:];assert re.fullmatch('NNN_L[0-9]{3}',a)and 1<=int(a[-3:])<=40 and kind in ['lean','link','audit']and not(E/a).exists()
guard=E/'NNN_CLIENT_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def event(x):
 with(E/'NNN_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict({'attempt':a},**x))+'\n')
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with(E/'NNN_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  event(dict(event='wait',reason='transport',retry=retry,submitted=submitted))
  if submitted:raise RuntimeError('Submitted: recover read-only, NEVER resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('STOP transport exhausted')
while True:
 r=ssh('python3',"""import subprocess,pathlib,json
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--no-pager'],text=True).splitlines();found=[]
for line in units:
 unit=line.split()[0];cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip();p=pathlib.Path('/sys/fs/cgroup'+cg)
 try:pids=(p/'cgroup.procs').read_text().split()
 except FileNotFoundError:continue
 for pid in pids:
  try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True))
  except(FileNotFoundError,PermissionError,ProcessLookupError):continue
  if cwd.startswith('/home/dombarker/project-offloads/codex-'):found.append(unit);break
print(json.dumps(dict(scopes=found,count=len(found))))
""");assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);event(dict(event='share_check'if x['count']<6 else'wait',reason='Stream A share',host=x))
 if x['count']<6:break
 time.sleep(180)
for retry in range(7):
 r=ssh('python3',f'import shutil,json;print(json.dumps(shutil.disk_usage({B!r})._asdict()))');assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);(E/(a+f'-disk-{retry}.json')).write_text(r.stdout)
 if x['free']>=40_000_000_000:break
 event(dict(event='wait',reason='disk below40GB',disk=x))
 if retry==6:raise RuntimeError('STOP disk')
 time.sleep(600)
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r})
with(b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r};print(p.read_text()if p.exists()else'MISSING');sys.exit(r.returncode)
''');(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed')is True:break
 if(r.returncode==78 or ad.get('allowed')is False)and retry<10:
  event(dict(event='wait',reason='reservation refusal',exit=r.returncode,reservation=ad));time.sleep(180);continue
 raise RuntimeError('STOP admission')
files={};sources=[]
if kind=='lean':
 p=E/(target+'.lean');n='NNN_sources/'+target+'.lean';files[n]=p.read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNN_sources','-o','NNN_exports/'+target+'.olean',n]
 if target=='NNN_RuntimeScan':command+=['-c','NNN_native/NNN_RuntimeScan.c']
elif kind=='link':
 sources=['NNN_native/NNN_RuntimeScan.c'];command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NNN_native/NNN_RuntimeScan',*sources]
else:
 sources=['NNN_EXPECTED_IMPORTS.jsonl'] if target=='combined' else ['NNN_raw_audit.py'];files[sources[0]]=(E/sources[0]).read_text();command=['NNN_native/NNN_RuntimeScan','scan'] if target=='combined' else ['python3','NNN_raw_audit.py']
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NNN_tmp',LEAN_PATH=':'.join(json.loads((E/'NNN_PATHS.json').read_text()))),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=bool(subprocess.check_output(['git','status','--porcelain'],text=True)),deps_fingerprint={},expected_time='Focused import elaboration'if kind=='lean'else'Optimized linker'if kind=='link'else'Raw ax2 traversal / coherence scan')
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
for n in ['NNN_native','NNN_sources','NNN_tmp']:(b/n).mkdir(exist_ok=True)
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 if not(b/n).exists():shutil.copy2(w/n,b/n)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules+=re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
rels=set()
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root))for z in p.rglob('*')if z.is_file()and any(str(z).endswith(s)for s in['.olean','.olean.private','.olean.server','.ir']))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
rels.update(n.replace('.','/')+'.olean'for n in modules)
for rel in sorted(rels):
 p=next((Path(root)/rel for root in roots if(Path(root)/rel).is_file()),None);assert p is not None,rel
 for z in[p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
event(dict(event='submission',kind=kind,target=target));r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,base64,hashlib,lzma
b=Path({B!r});a={a!r};names=[p for p in(b/a).rglob('*')if p.is_file()]+[b/(a+'.json')]
if {kind!r}=='lean':
 q=b/(a+'-memory-review.json')
 if q.exists():names.append(q)
 p=b/'NNN_exports'/({target!r}+'.olean')
 if p.exists():
  q=b/(a+'-object.json');q.write_text(json.dumps(dict(module={target!r},path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)));names.append(q)
if {kind!r}=='audit':
 p=b/'NNN_LOADED_scan.jsonl'
 if p.exists():names.append(p)
 for p in b.glob('NEP_*_REACHABLE.txt'):
  import lzma
  raw=p.read_bytes();q=b/'NNN_raw'/(p.name+'.xz');q.parent.mkdir(exist_ok=True);q.write_bytes(lzma.compress(raw,preset=1));t=Path(str(q)[:-3]+'.sha256');t.write_text(hashlib.sha256(raw).hexdigest()+'\\n');names +=[q,t]
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode()for p in names}}))
''');assert r.returncode==0,r.stderr
for n,v in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
assert(E/a/'receipt.json').exists(),'Missing receipt: never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items()if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json';event(dict(event='result',**entry))
with(E/'NNN_TRANSCRIPT.txt').open('a')as f:f.write(f"{a} {kind} {target}: exit {rc['exit_status']}, wall {rc['wall_seconds']:.3f}s, RSS {rc['peak_rss_kib']}KiB, swaps {rc['swaps']}.\n")
print(json.dumps({k:rc[k]for k in['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
