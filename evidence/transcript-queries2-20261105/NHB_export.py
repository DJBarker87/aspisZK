"""Retain checked owned objects and recover metadata; no build is launched."""
from pathlib import Path
import subprocess,json,time,base64,lzma,sys
final_events="--final-events" in sys.argv
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-transcript-queries2-20261105';C='/home/dombarker/project-offloads/codex-cx-transcript-queries-cache-20261104'
mods=[]
for p in E.glob('NHB_L[0-9][0-9][0-9]/receipt.json'):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0 and 'Inspect' not in r['module']:mods.append(r['module'])
code=f'''from pathlib import Path
import json,hashlib,shutil,subprocess,base64
b=Path({B!r});c=Path({C!r});ad=b/'NHB_EXPORT-reservation.json'
for retry in range(11):
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(ad)],capture_output=True,text=True)
 a=json.loads(ad.read_text())
 if r.returncode==0 and a.get('allowed') is True:break
 assert r.returncode==78 or a.get('allowed') is False
 if retry<10:__import__('time').sleep(60)
else:raise RuntimeError('No admission; no export/cleanup performed')
out=c/('NHB_final_events_20261105' if {final_events!r} else 'NHB_exports_20261105');out.mkdir(exist_ok=True);rows=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for mod in sorted(set({mods!r})):
 for p in sorted((b/'NHB_objects').glob(mod+'.*')):
  if not ('.olean' in p.name or p.suffix=='.ir'):continue
  q=out/p.name;copied=not q.exists()
  if q.exists():assert sha(q)==sha(p),'Never overwrite a different retained object'
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),bytes=q.stat().st_size,sha256=sha(q),new_copy=copied))
p=b/'NHB_native/NHB_ProofDriver'
# Retain binary once in its owned workspace; cache only the small object forest.
binary_pin=dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
extras={{}}
for n in ['NHB_CACHE_IMPORTS.json.xz']:
 p=b/n
 if p.exists():extras[n]=base64.b64encode(p.read_bytes()).decode()
lock=b/'NHB_src/Cargo.lock'
summary=dict(binary_retained_once=binary_pin,exported=rows,export_bytes=sum(r['bytes'] for r in rows),new_copy_bytes=sum(r['bytes'] for r in rows if r['new_copy']),admission=dict(exit=r.returncode,allowed=a['allowed'],reservation_sha256=sha(ad)),extras=extras,final_lock_sha256=sha(lock),disk_before=shutil.disk_usage(b)._asdict())
assert summary['final_lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
# Only owned build target/TMPDIR, after all source/log/artifact pins are retained.
removed=[]
for n in ['NHB_target','NHB_tmp']:
 p=b/n
 if p.exists():shutil.rmtree(p);removed.append(str(p))
summary['removed_owned_scratch']=removed;summary['disk_after']=shutil.disk_usage(b)._asdict()
(b/('NHB_FINAL_EVENTS_HOST.json' if {final_events!r} else 'NHB_FINAL_HOST.json')).write_text(json.dumps(summary,indent=1)+'\\n')
print(json.dumps(summary))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
if r.returncode==255:
 for _ in range(10):
  time.sleep(60)
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'cat '+B+('/NHB_FINAL_EVENTS_HOST.json' if final_events else '/NHB_FINAL_HOST.json')],text=True,capture_output=True)
  if r.returncode==0:break
assert r.returncode==0,(r.returncode,r.stderr)
d=json.loads(r.stdout)
for n,s in d.pop('extras').items():(E/n).write_bytes(base64.b64decode(s))
(E/('NHB_FINAL_EVENTS_HOST.json' if final_events else 'NHB_FINAL_HOST.json')).write_text(json.dumps(d,indent=1)+'\n')
print(json.dumps({'exported':len(d['exported']),'bytes':d['export_bytes'],'final_lock':d['final_lock_sha256'],'removed_owned_scratch':d['removed_owned_scratch']}))
