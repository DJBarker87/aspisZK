"""Deduplicate identical objects only inside the explicitly owned ledger8 cache.

All paths and bytes survive. Atomic link replacement changes only NGZ_flat copies;
no read-only predecessor cache, key, source or other workspace is modified.
"""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger9-20261105'
code='''from pathlib import Path
import json,hashlib,os,subprocess
b=Path(B);owned=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104');flat=owned/'NGZ_flat'
assert all(json.loads((b/('NGZ_L'+str(i).zfill(3))/'receipt.json').read_text())['exit_status']==0 for i in range(35,41))
before=subprocess.check_output(['du','-sk',str(owned)],text=True);index={};records=[]
for p in owned.rglob('*'):
 if flat in p.parents or not p.is_file() or not any(s in p.name for s in ['.olean','.ir']):continue
 index.setdefault((p.name,p.stat().st_size),[]).append(p)
for p in flat.rglob('*'):
 if not p.is_file() or not any(s in p.name for s in ['.olean','.ir']):continue
 options=index.get((p.name,p.stat().st_size),[])
 if not options:continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 for q in options:
  if p.stat().st_ino==q.stat().st_ino:break
  if hashlib.sha256(q.read_bytes()).hexdigest()!=h:continue
  tmp=p.with_name(p.name+'.NGZ_link');assert not tmp.exists();os.link(q,tmp)
  assert hashlib.sha256(tmp.read_bytes()).hexdigest()==h
  os.replace(tmp,p);assert hashlib.sha256(p.read_bytes()).hexdigest()==h
  records.append(dict(path=str(p),retained_identical_source=str(q),sha256=h,bytes=p.stat().st_size));break
after=subprocess.check_output(['du','-sk',str(owned)],text=True)
(b/'NGZ_DEDUPLICATION.json').write_text(json.dumps(dict(only_owned_NGZ_flat_replaced=True,all_paths_and_bytes_retained=True,cache_deleted=False,before=before,after=after,replacements=records),indent=1));print(len(records),before,after)
'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input='B='+repr(B)+'\n'+code,text=True,capture_output=True);(E/'NGZ_DEDUPLICATION_TRANSPORT.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/NGZ_DEDUPLICATION.json'],capture_output=True);assert r.returncode==0;(E/'NGZ_DEDUPLICATION.json').write_bytes(r.stdout);print('Owned-cache paths and hashes retained')
