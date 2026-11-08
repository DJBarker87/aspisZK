"""Job-owned serial client; unchanged host reservation, launcher and Lean shim."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if(E/'NNM_HOLD').exists():sys.exit(75)
a,kind,target=sys.argv[1:];assert re.fullmatch('NNM_L[0-9]{3}',a) and 1<=int(a[-3:])<=60 and not(E/a).exists()
guard=E/'NNM_CLIENT_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def event(x):
 with(E/'NNM_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict({"attempt":a},**x))+'\n')
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with(E/'NNM_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  event(dict(event='wait',reason='transport',retry=retry,submitted=submitted))
  if submitted:raise RuntimeError('Submitted: recover read-only, NEVER resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('STOP transport exhausted')
r=ssh('python3',f'from pathlib import Path;Path({B!r}).mkdir(exist_ok=True)');assert r.returncode==0,r.stderr
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
 for _ in range(10):time.sleep(60)
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
if kind=='seed':
 names=['NNM_seed_host.py','NNM_SEED_CONFIG.json']
 command=['python3','NNM_seed_host.py']
elif kind=='rsl':
 names=['NNM_rev4_sources/'+target+'.lean'];files[names[0]]=(E/'NNM_rev4_sources'/(target+'.lean')).read_text();sources=names[:]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNM_rev4_sources','-o','NNM_rev4/'+target+'.olean',names[0]]
elif kind=='lean':
 names=['NNM_generated/'+target+'.lean'];p=E/(target+'.lean');files[names[0]]=p.read_text();sources=names[:]
 if target=='NNM_Statements':names+=['NNM_AUDIT_ROOTS.json']
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNM_generated','-o','NNM_objects/'+target+'.olean',names[0]]
 if target=='NNM_Driver':command+=['-c','NNM_native/NNM_Driver.c']
elif kind=='link':
 names=['NNM_native/NNM_Driver.c','NNM_native/NFA_WALKER.c','NNM_native/NFA_MemoryLimit.c'];sources=names[:]
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NNM_native/NNM_Driver',*names]
elif kind=='audit':
 names=['NNM_batch.py','NNM_AUDIT_ROOTS.json','NNM_AUDIT_MODULES.json','NNM_EXPECTED_IMPORTS.jsonl']
 if target=='retention'or target.endswith('-pin'):names+=['NNM_pin.py']
 command=['python3','NNM_batch.py',target]
else:raise ValueError(kind)
for n in names:
 if n not in files and(E/Path(n).name).is_file():files[n]=(E/Path(n).name).read_text()
sources=list(dict.fromkeys(sources+names))
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NNM_tmp',CARGO_TARGET_DIR=B+'/NNM_target',LEAN_PATH=':'.join([B+'/NNM_objects']+json.loads((E/'NNM_PATHS.json').read_text()))),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Pinned cache IO'if kind=='seed'else'Focused import elaboration'if kind=='lean'else'Optimized linker'if kind=='link'else'Raw ax2 traversal / coherence scan')
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
for n in ['NNM_native','NNM_objects','NNM_rev4','NNM_tmp']: (b/n).mkdir(exist_ok=True)
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 if not(b/n).exists():shutil.copy2(w/n,b/n)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=b/'NNM_native'/n
 if not p.exists():shutil.copy2('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_native_seed/'+n,p)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind'] in ['lean','rsl']:modules+=re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules+=['NNM_COMBINED_IMPORT']
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
import json,lzma,hashlib,base64
b=Path({B!r});a={a!r};names=[p for p in(b/a).rglob('*')if p.is_file()]+[b/(a+'.json')]
if {kind!r}=='audit':
 names += [p for p in(b/'NNM_audit'/{target!r}).rglob('*')if p.is_file()]
 for p in(b/'NNM_audit'/{target!r}).glob('*.json'):
  for row in json.loads(p.read_text()).get('results',[]):
   q=b/('NEP_'+p.stem+'_'+row['root']+'_REACHABLE.txt')
   if q.exists():
    raw=q.read_bytes();d=b/'NNM_raw';d.mkdir(exist_ok=True);z=d/(q.name+'.xz');z.write_bytes(lzma.compress(raw,preset=1));s=d/(q.name+'.sha256');s.write_text(hashlib.sha256(raw).hexdigest()+'\\n');names+=[z,s]
 for n in ['NNM_LOADED_scan.jsonl','NNM_TOOL_PINS.json','NNM_CLOSURE_PINS.json.xz','NNM_CLOSURE_PINS.json.sha256','NNM_EXPORT.json','NNM_PREDECESSOR_COMPARISON.json','NNM_GATE_INTEGRITY.json']:
  if(b/n).is_file():names.append(b/n)
if {kind!r}=='seed':
 names += [b/n for n in ['NNM_CACHE_IMPORTS.json.xz','NNM_CACHE_IMPORTS.json.sha256','NNM_SOURCE_PINS.json','NNM_RAW_BINARY.json']if(b/n).is_file()]
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode()for p in names}}))
''');assert r.returncode==0,r.stderr
for n,v in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
assert(E/a/'receipt.json').exists(),'Missing receipt: never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items()if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json';event(dict(event='result',**entry))
with(E/'NNM_TRANSCRIPT.txt').open('a')as f:f.write(f"{a} {kind} {target}: exit {rc['exit_status']}, wall {rc['wall_seconds']:.3f}s, RSS {rc['peak_rss_kib']}KiB, swaps {rc['swaps']}.\n")
print(json.dumps({k:rc[k]for k in['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
