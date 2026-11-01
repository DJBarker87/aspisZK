"""Preserve accepted own objects, then remove only rebuildable own scratch."""
from pathlib import Path
import subprocess,json,hashlib,time,shlex
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose2-20261029';H='dombarker@100.108.41.90';a='NEE_ARCHIVE'
assert not (E/a).exists() and not (E/'NEE_ACTIVE.json').exists()
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,text=True,capture_output=True)
  with (E/'NEE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('STOP persistent transport')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  for _ in range(3):time.sleep(60)
  continue
 raise SystemExit('STOP admission')
spec={}
for line in (E/'NEE_ATTEMPTS.jsonl').read_text().splitlines():
 rc=json.loads(line)
 if rc['kind']=='lean' and rc['exit_status']==0:
  m=rc['module'];p=E/(m.replace('.','/')+'.lean')
  if p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==rc['source_hashes']['NEE_generated/'+m.replace('.','/')+'.lean']:spec[m]=hashlib.sha256(p.read_bytes()).hexdigest()
source=f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});spec={spec!r};cache=b.parent/'codex-cx-slice-s-compose2-cache-20261029';dest=cache/'NEE_final_objects_20261101'
assert cache.is_dir() and not dest.exists();rows=[]
for name,expected in spec.items():
 rel=name.replace('.','/');src=b/'NEE_generated'/(rel+'.lean');obj=b/'NEE_objects'/(rel+'.olean')
 assert src.exists() and hashlib.sha256(src.read_bytes()).hexdigest()==expected and obj.exists(),name
 for suffix,root in [('.lean',b/'NEE_generated'),('.olean',b/'NEE_objects'),('.ilean',b/'NEE_objects')]:
  p=root/(rel+suffix)
  if not p.exists():continue
  q=dest/(rel+suffix);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  digest=hashlib.sha256(q.read_bytes()).hexdigest();assert digest==hashlib.sha256(p.read_bytes()).hexdigest()
  rows.append(dict(module=name,path=str(q),sha256=digest,bytes=q.stat().st_size))
manifest=dict(cache=str(dest),objects=rows,cleanup=[])
for name in ['NEE_target','NEE_objects','NEE_tmp']:
 p=b/name;assert p.parent==b and not p.is_symlink()
 if p.exists():shutil.rmtree(p)
 manifest['cleanup'].append(dict(path=str(p),absent=not p.exists()))
(b/'NEE_CACHE_FINAL.json').write_text(json.dumps(manifest,indent=1)+'\\n')
print(json.dumps(dict(copied=len(rows),modules=len(spec),cache=str(dest),cleanup=manifest['cleanup'])))
'''
cfg=dict(attempt=a,kind='python-cache-archive',module='NEE_cache_archive',sources=['NEE_archive_host.py'],command=['python3','NEE_archive_host.py'],env=dict(PATH='/usr/bin:/bin'),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True)
(E/'NEE_archive_host.py.txt').write_text(source);(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
files={'NEE_archive_host.py':source,a+'.json':json.dumps(cfg)}
code=f'''from pathlib import Path
import json
b=Path({B!r})
for n,s in json.loads({json.dumps(files)!r}).items():(b/n).write_text(s)
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log','NEE_CACHE_FINAL.json']!r} if (b/n).exists()}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'recover read-only; never resubmit'
rc=json.loads(out[a+'/receipt.json']);print(json.dumps({k:rc[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']}));print(out[a+'/stdout.log'])
assert rc['exit_status']==0
