"""NOF-owned serial client for the unchanged S2W launcher (adapted from NNY_run.py; caps identical).
Usage: python3 NOF_run.py NOF_Lnnn STAGE lean TARGET
STAGE in P0..P4 with caps 3/4/6/2/5; total 20.  A stage may start only when every earlier
stage has NOF_Pk_CLOSED.json (an exhausted stage stops the whole job)."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-a2-20261108';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NOF_HOLD').exists():sys.exit(75)
guard=E/'NOF_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,stage,kind,target=sys.argv[1:];assert re.fullmatch('NOF_L[0-9]{3}',a) and 1<=int(a[-3:])<=20 and not (E/a).exists()
CAPS={'P0':3,'P1':4,'AUDIT':2,'P2':6,'P3':2,'P4':5,'P5':4}; assert stage in CAPS
used={};
for n in ['NOF_ATTEMPTS.jsonl','NOF_TRANSPORT.jsonl']:
 p=E/n
 if not p.exists():continue
 for line in p.read_text().splitlines():
  row=json.loads(line)
  if 'exit_status' in row or row.get('submitted') is True:used[row['attempt']]=row.get('continuation_stage',row.get('stage'))
assert len(used)<20,'NOF allowance 20 scopes exhausted'
assert sum(1 for s in used.values() if s==stage)<CAPS[stage],stage+' cap exhausted: STOP the whole job'
need=2 if stage=='AUDIT' else int(stage[1])
for k in range(need):
 assert (E/f'NOF_P{k}_CLOSED.json').exists(),f'P{k} not closed: STOP'
if stage in ['P2','P3','P4']:assert (E/'NOF_AUDIT_CLEAR.json').exists(),'lead-ordered slot audit must clear before P2'

def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NOF_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,stage=stage,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr[-2000:]))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
while True:
 r=ssh('python3',"""import subprocess,pathlib,json
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--no-pager'],text=True).splitlines();found=[]
for line in units:
 unit=line.split()[0];cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip();p=pathlib.Path('/sys/fs/cgroup'+cg)
 try:pids=(p/'cgroup.procs').read_text().split()
 except FileNotFoundError:continue
 for pid in pids:
  try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True))
  except (FileNotFoundError,PermissionError,ProcessLookupError):continue
  if cwd.startswith('/home/dombarker/project-offloads/codex-'):found.append(unit);break
lean=subprocess.run(['pgrep','-c','-x','lean'],capture_output=True,text=True).stdout.strip() or '0'
print(json.dumps(dict(scopes=found,count=len(found),lean_processes=int(lean))))
""")
 assert r.returncode==0,r.stderr
 share_info=json.loads(r.stdout)
 ok=share_info['count']<6 and share_info['lean_processes']<6
 with (E/'NOF_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,stage=stage,event='share_check' if ok else 'wait',reason='scope share and whole-host lean count',host=share_info))+'\n')
 if ok:break
 time.sleep(180)
for disk_retry in range(7):
 disk=ssh('python3',"import shutil,json;print(json.dumps(shutil.disk_usage('/')._asdict()))")
 assert disk.returncode==0,disk.stderr
 disk_info=json.loads(disk.stdout)
 (E/(a+'-disk-'+str(disk_retry)+'.json')).write_text(json.dumps(disk_info))
 if disk_info['free']>=40_000_000_000:break
 if disk_retry==6:raise RuntimeError('STOP host free below40GB after six waits')
 for _ in range(10):time.sleep(60)
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r})
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r}; print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  with (E/'NOF_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,stage=stage,event='wait',reason='reservation refusal',exit=r.returncode,reservation=ad))+'\n')
  print('reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP admission')
files={};sources=[]
assert kind in ['lean','audit'],kind
pin_modules=None
if kind=='lean':
 src=E/(target+'.lean')
 if not src.exists():src=E/'NOF_dependency_inputs'/(target+'.lean')
 n='NOF_generated/'+target.replace('.','/')+'.lean';files[n]=src.read_text();sources=[n]
 out_obj='NOF_objects/'+target.replace('.','/')+'.olean'
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NOF_generated','-o',out_obj,n]
else:
 files['NOF_raw_audit.py']=(E/'NOF_raw_audit.py').read_text();sources=['NOF_raw_audit.py']
 out_obj='NOF_objects/NOF_audit_no_output_'+a
 command=['python3','NOF_raw_audit.py'];pin_modules=[target]
overlays=json.loads((E/'NNY_RUN5B_PATHS.json').read_text())
config=dict(continuation_stage=stage,attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NOF_tmp',CARGO_TARGET_DIR=B+'/NOF_target',LEAN_PATH=':'.join([B+'/NOF_objects',B+'/NNY_objects']+(json.loads((E/'NOF_EXTRA_PATHS.json').read_text()) if (E/'NOF_EXTRA_PATHS.json').exists() else [])+overlays)),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=bool(subprocess.check_output(['git','status','--porcelain','--','.'],text=True).strip()),deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Raw ax2 traversal with pinned ledger30 walker',pin_modules=pin_modules)
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,os
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;assert not p.is_symlink();p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NOF_objects').mkdir(exist_ok=True);(b/'NOF_tmp').mkdir(exist_ok=True)
o=b/{out_obj!r};o.parent.mkdir(parents=True,exist_ok=True)
assert not o.is_symlink() and not o.exists(),'refusing to overwrite existing or symlinked output '+str(o)
assert os.path.realpath(o.parent).startswith(str(b/'NOF_objects')),'output dir escapes NOF_objects'
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=x.get('pin_modules') or re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
def resolve(m):
 parts=m.split('.')
 for root in roots:
  if (Path(root)/parts[0]).is_dir() or Path(root,parts[0]+'.olean').is_file():return Path(root,*parts).with_suffix('.olean')
rels=set()
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
sel=[next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None) for rel in sorted(rels)]
sel+=[resolve(m) for m in modules]
for p in sel:
 assert p is not None and p.is_file(),str(p)
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'realpath':os.path.realpath(z)}}
x['deps_fingerprint']={{'selected_objects':pins,'resolution':'Lean package-root rule (first root holding the top-level component)','cache_imports_manifest_sha256':hashlib.sha256(Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111/NNH_CACHE_IMPORTS.json.xz').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']+([str(p.relative_to(b)) for p in (b/'NOF_audit2').glob('NEP_*') if p.is_file() and p.stat().st_size<20_000_000] if {kind!r}=='audit' else [])
out={{n:(b/n).read_text() for n in names}}
o=b/{out_obj!r}
if o.is_file():out[a+'/OBJECT_PIN.json']=json.dumps(dict(path=str(o),sha256=hashlib.sha256(o.read_bytes()).hexdigest(),bytes=o.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
log=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
entry['sorryAx_in_log']='sorryAx' in log
entry['pass']=rc['exit_status']==0 and json.loads((E/(a+'-admission.json')).read_text())['reservation'].get('allowed') is True and 'sorryAx' not in log
with (E/'NOF_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
with (E/'NOF_COMPILE.tsv').open('a') as f:f.write('\t'.join(str(rc[k]) for k in ['attempt','continuation_stage','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision'])+'\t'+json.dumps(rc.get('print_axioms'))+'\t'+a+'/receipt.json\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),'pass=',entry['pass']);sys.exit(0 if entry['pass'] else 1)
