"""Preserve exact successful private objects, then remove own compiled scratch."""
from pathlib import Path
import subprocess,json,time,hashlib,shlex
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose-20261029';H='dombarker@100.108.41.90';a='NED_ARCHIVE'
assert not (E/'NED_ACTIVE.json').exists()
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=stdin,text=True,capture_output=True)
  with (E/'NED_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('transport exhausted before submission')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  for _ in range(3):time.sleep(60)
  continue
 raise SystemExit('admission refused')
spec={}
for p in sorted(E.glob('NED_L*/receipt.json')):
 r=json.loads(p.read_text());s=p.parent/'NED_SOURCE.lean.txt'
 if r['exit_status']==0 and s.exists():spec[r['module']]=hashlib.sha256(s.read_bytes()).hexdigest()
source='''from pathlib import Path
import json,hashlib,shutil
b=Path(B);cache=b.parent/'codex-cx-slice-s-compose-cache-20261029';dest=cache/'NED_final_objects_20261029'
assert b.name=='codex-cx-slice-s-compose-20261029' and cache.is_dir()
rows=[];skipped=[]
for name,expected in SPEC.items():
 rel=name.replace('.','/');src=b/'NED_generated'/(rel+'.lean');obj=b/'NED_objects'/(rel+'.olean')
 if not src.exists() or hashlib.sha256(src.read_bytes()).hexdigest()!=expected or not obj.exists():
  skipped.append(name);continue
 if name=='NED_NativeRoots':skipped.append(name);continue
 for suffix,root in [('.lean',b/'NED_generated'),('.olean',b/'NED_objects'),('.ilean',b/'NED_objects')]:
  p=root/(rel+suffix)
  if not p.exists():continue
  q=dest/(rel+suffix);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  digest=hashlib.sha256(q.read_bytes()).hexdigest();assert digest==hashlib.sha256(p.read_bytes()).hexdigest()
  rows.append(dict(module=name,path=str(q),sha256=digest,bytes=q.stat().st_size))
manifest=dict(cache=str(dest),objects=rows,skipped=skipped,cleanup=[])
for name in ['NED_target','NED_objects','NED_tmp']:
 p=b/name;assert p.parent==b and p.name==name and not p.is_symlink()
 if p.exists():shutil.rmtree(p)
 manifest['cleanup'].append(dict(path=str(p),absent=not p.exists()))
(b/'NED_CACHE_FINAL.json').write_text(json.dumps(manifest,indent=1)+'\\n')
print(json.dumps(dict(copied=len(rows),skipped=skipped,cleanup=manifest['cleanup'])))
'''
source='B='+repr(B)+'\nSPEC='+repr(spec)+'\n'+source
cfg=dict(attempt=a,kind='python-cache-archive',module='NED_cache_archive',sources=['NED_archive_host.py'],command=['python3','NED_archive_host.py'],env=dict(PATH='/usr/bin:/bin'),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n');(E/'NED_archive_host.py.txt').write_text(source)
files={'NED_archive_host.py':source,a+'.json':json.dumps(cfg)}
code=f'''from pathlib import Path
import json
b=Path({B!r})
for n,s in json.loads({json.dumps(files)!r}).items():(b/n).write_text(s)
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log','NED_CACHE_FINAL.json']!r} if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'recover read-only; never resubmit'
rc=json.loads(out[a+'/receipt.json']);assert rc['exit_status']==0,rc
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}))
