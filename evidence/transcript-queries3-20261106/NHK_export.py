"""Retain only owned small Lean exports and once-pinned audit binary; remove own Rust/temp scratch."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-transcript-queries3-20261106'
def ssh(code):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
  with (E/'NHK_EXPORT_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if retry<10:time.sleep(60)
 raise RuntimeError('transport exhausted')
for retry in range(11):
 r=ssh(f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});p=b/'NHK_EXPORT-reservation.json'
with (b/'NHK_EXPORT-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/f'NHK_EXPORT-barrier-{retry}.log').write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise RuntimeError('admission rejected')
r=ssh(f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});c=Path('/home/dombarker/project-offloads/codex-cx-transcript-queries-cache-20261104/NHK_exports_20261106');c.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=[];before=shutil.disk_usage(b)._asdict()
for p in sorted((b/'NHK_objects').iterdir()):
 assert p.name.startswith('NHK_') and p.is_file(),p
 dst=c/p.name
 if dst.exists():assert sha(dst)==sha(p)
 else:shutil.copy2(p,dst)
 rows.append(dict(source=str(p),destination=str(dst),bytes=p.stat().st_size,sha256=sha(p)))
binary=b/'NHK_native/NHK_ProofDriver';binarypin=dict(path=str(binary),bytes=binary.stat().st_size,sha256=sha(binary))
lock=sha(b/'NHK_src/Cargo.lock');assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
removed=[]
for name in ['NHK_target','NHK_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
print(json.dumps(dict(admission_exit=0,admission={ad!r},exports=rows,export_bytes=sum(r['bytes'] for r in rows),audit_binary_retained_once=binarypin,final_lock_sha256=lock,removed_owned_scratch=removed,disk_before=before,disk_after=shutil.disk_usage(b)._asdict()),indent=2))
''')
assert r.returncode==0,r.stderr
(E/'NHK_FINAL_HOST.json').write_text(r.stdout);x=json.loads(r.stdout);print(json.dumps(dict(export_files=len(x['exports']),export_bytes=x['export_bytes'],final_lock_sha256=x['final_lock_sha256'],removed_owned_scratch=x['removed_owned_scratch'])))
