"""Archive own accepted objects and clean only rebuildable own build scratch."""
from pathlib import Path
import json,subprocess,hashlib,time,sys,shlex
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose5-20261029';H='dombarker@100.108.41.90';a='NEM_ARCHIVE'
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,text=True,capture_output=True)
  with (E/'NEM_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('STOP persistent transport')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,sys
b=Path({B!r})
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print((b/{(a+'-barrier-'+str(retry)+'.log')!r}).read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise SystemExit('STOP archive admission')
accepted={}
for p in sorted(E.glob('NEM_L*/receipt.json')):
 rc=json.loads(p.read_text())
 if rc['exit_status']!=0:continue
 module=rc['module'];source=E/(module+'.lean')
 if not source.exists():continue
 expected=hashlib.sha256(source.read_bytes()).hexdigest()
 if rc['source_hashes'].get('NEM_generated/'+module+'.lean')==expected:accepted[module]=expected
assert len(accepted)==14,accepted
host='''from pathlib import Path
import json,hashlib,shutil
b=Path(__file__).resolve().parent;dest=b.parent/'codex-cx-slice-s-compose5-cache-20261029/NEM_final_objects_20261102'
dest.mkdir(parents=True,exist_ok=False);accepted=ACCEPTED;copied=[]
for module,expected in accepted.items():
 src=b/'NEM_generated'/(module+'.lean');obj=b/'NEM_objects'/(module+'.olean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==expected
 for p in [src,obj]:
  q=dest/p.name;shutil.copyfile(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  copied.append(dict(source=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
# Inventory only this job's scratch. Permanent caches and frozen inputs stay.
tmp=b/'NEM_tmp';solver_files=[dict(path=str(p),bytes=p.stat().st_size) for p in tmp.rglob('*') if p.is_file()]
removed=[]
for name in ['NEM_target','NEM_objects','NEM_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
out=dict(copied=copied,solver_temp_inventory=solver_files,removed_only_own_rebuildable_scratch=removed,permanent_cache_retained=str(dest),frozen_lock_sha256=hashlib.sha256((b/'NEM_src/Cargo.lock').read_bytes()).hexdigest())
(b/'NEM_CACHE_FINAL.json').write_text(json.dumps(out,indent=1)+'\\n');print(json.dumps(dict(copied=len(copied),removed=removed)))
'''.replace('ACCEPTED',repr(accepted))
cfg=dict(attempt=a,kind='archive',module='archive own accepted objects',sources=['NEM_archive_host.py'],command=['python3','NEM_archive_host.py'],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin'))
files={'NEM_archive_host.py':host,a+'.json':json.dumps(cfg)}
code=f'''from pathlib import Path
import json
b=Path({B!r})
for n,s in json.loads({json.dumps(files)!r}).items():(b/n).write_text(s)
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n');(E/'NEM_archive_host.py').write_text(host)
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log','NEM_CACHE_FINAL.json']!r} if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr;out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'submitted archive unresolved; never resubmit'
rc=json.loads(out[a+'/receipt.json']);entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=dict(path=str(E/a/'receipt.json'),sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest())
with (E/'NEM_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
