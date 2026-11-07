"""PCI serial client for unchanged S2W launcher; own validation only."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,os,atexit,lzma
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-pc-deposit-children2-20261110';C='/home/dombarker/project-offloads/codex-pc-deposit-children2-cache-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a=sys.argv[1];task=json.loads((E/'PCI_TASKS.json').read_text())[a];kind=task['kind'];num=int(a[-3:]);used=[json.loads(l) for l in (E/'PCI_ATTEMPTS.jsonl').read_text().splitlines()]
category=lambda k:'lean' if k in ['lean','link','audit'] else k
assert sum(category(r['kind'])==category(kind) for r in used)<dict(lean=120,kani=130,extract=14)[category(kind)]
assert 'extra_rustflags' not in task,'use explicit env.RUSTFLAGS; ignored flags forbidden'
assert not (E/a/'receipt.json').exists(),'terminal receipt exists; no rerun'
transport_records=[json.loads(l) for l in (E/'PCI_TRANSPORT.jsonl').read_text().splitlines()] if (E/'PCI_TRANSPORT.jsonl').exists() else []
assert not any(r.get('attempt')==a and r.get('submitted') is True for r in transport_records),'already submitted; recover read-only, never resubmit'
guard=E/'PCI_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=data,capture_output=True,text=True)
  with (E/'PCI_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for retry in range(7):
 r=ssh('python3',f'import shutil,json;print(json.dumps(shutil.disk_usage({B!r})._asdict()))');assert r.returncode==0
 disk=json.loads(r.stdout);(E/(a+f'-disk-{retry}.json')).write_text(json.dumps(disk))
 if disk['free']>=40_000_000_000:break
 if retry==6:raise RuntimeError('STOP host disk below40GB after six waits')
 for _ in range(10):time.sleep(60)
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r};print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP infrastructure missing admission JSON')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print(a+' reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP infrastructure admission')
files={n:(E/p).read_text() for n,p in task.get('files',{}).items()};sources=list(files)
if kind=='kani':
 import re
 for n,text in files.items():
  if n.endswith('.rs'):
   for dep in re.findall(r'path="(PCI_[0-9]+\.rs)"',text):
    assert str(Path(n).parent/dep) in files,'own cfg module missing upload: '+dep

if kind=='lean':
 target=task['target'];n='PCI_generated/'+target.replace('.','/')+'.lean';files[n]=(E/(target+'.lean')).read_text();sources.append(n)
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','PCI_generated','-o','PCI_objects/'+target.replace('.','/')+'.olean',n]
 if task.get('native'):command+=['-c','PCI_native/'+target+'.c']
else:command=task['command'];target=task['target']
env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/PCI_tmp',LEAN_PATH=B+'/PCI_objects:'+C,CARGO_NET_OFFLINE='true',CARGO_INCREMENTAL='0',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=B+'/PCI_target',RUSTFLAGS='-C link-arg=-Wl,--threads=1')
env.update(task.get('env',{}))
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time=task.get('expected_time','Focused proof / optimized compile; no heavy field arithmetic'))
if kind=='kani':
 cfg['native_command']=task['native_command'];cfg['pool_features']=task['pool_features']
files[a+'.json']=json.dumps(cfg)
for n,s in files.items():p=E/a/'sources'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,lzma,shutil
b=Path({B!r});c=Path({C!r});files=json.loads({json.dumps(files)!r})
for n,s in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
(b/'PCI_objects'/{target.replace('.', '/')!r}).parent.mkdir(parents=True,exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text())
if x['kind']=='kani':
 srcpins=json.loads((b/'PCI_SOURCE_PINS.json').read_text())
 for n in files:
  if n.startswith('PCI_src/'):srcpins[n[len('PCI_src/'):]]=hashlib.sha256((b/n).read_bytes()).hexdigest()
 (b/'PCI_SOURCE_PINS.json').write_text(json.dumps(srcpins))
pins=json.loads(lzma.decompress((b/'PCI_IMPORTS.json.xz').read_bytes()))
for rel,v in pins.items():
 p=c/rel
 assert p.exists() and p.stat().st_size==v['bytes'],rel
own={{str(p):dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in (b/'PCI_objects').rglob('*') if p.is_file()}}
x['deps_fingerprint']={{'seed_manifest_sha256':hashlib.sha256((b/'PCI_IMPORTS.json.xz').read_bytes()).hexdigest(),'selected_objects':own,'seed_note':'selected input files pinned by PCI_IMPORTS.json.xz, including all selected Aeneas objects and sidecars'}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']+{task.get('collect',[])!r}
print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in names if (b/n).is_file()}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(__import__('base64').b64decode(s))
assert a+'/receipt.json' in out,'missing receipt after submission; recover only'
rc=json.loads(__import__('base64').b64decode(out[a+'/receipt.json']));assert rc['attempt']==a
with (E/'PCI_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc.get(k) for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
# Details stay in evidence; terminal summary only.

if kind in ['lean','link','audit'] and rc['exit_status']!=0:sys.exit(1)
