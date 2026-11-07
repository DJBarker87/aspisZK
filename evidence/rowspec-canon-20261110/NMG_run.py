from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-rowspec-canon-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,target=sys.argv[1:];assert re.fullmatch('NMG_L[0-9]{3}',a) and 1<=int(a[-3:])<=100 and not (E/a).exists()
guard=E/'NMG_CLIENT_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NMG_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for retry in range(7):
 r=ssh('python3',"import shutil,json;print(json.dumps(shutil.disk_usage("+repr(B)+")._asdict()))");assert r.returncode==0,r.stderr
 disk=json.loads(r.stdout);(E/(a+'-disk-'+str(retry)+'.json')).write_text(json.dumps(disk))
 if disk['free']>=40_000_000_000:break
 if retry==6:raise RuntimeError('STOP host free below40GB')
 time.sleep(600)
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
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('NMG reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP admission')
n='NMG_generated/'+target+'.lean';files={n:(E/(target+'.lean')).read_text()}
config=dict(attempt=a,kind='lean',module=target,sources=[n],command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMG_generated','-o','NMG_objects/'+target+'.olean',n],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NMG_tmp',LEAN_PATH=':'.join([B+'/NMG_objects',B+'/NMG_seed']+json.loads((E/'NMG_SEED_PATHS.json').read_text()))),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused Lean proof elaboration')
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
mods=re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
rels=set(n.replace('.','/')+'.olean' for n in mods)
for stem in ['Aeneas','AeneasMeta']:
 for root in roots:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
for rel in sorted(rels):
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 assert p is not None,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NMG_CACHE_IMPORTS.json.xz').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True);(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json'];print(json.dumps({{n:(b/n).read_text() for n in names}}))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NMG_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
