"""Copy read-only predecessor caches; no shared infrastructure changes."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-slice-s-compose8-20261029'
code=r'''
from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose8-20261029');b.mkdir(exist_ok=True)
p=b/'NEX_SETUP-barrier.log';q=b/'NEX_SETUP-reservation.json'
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text(),flush=True)
assert r.returncode==0 and json.loads(q.read_text()).get('allowed') is True, 'admission refused'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cache=b.parent/'codex-cx-slice-s-compose8-cache-20261029';cache.mkdir(exist_ok=True)
records=[]
# The predecessor cache already contains accepted objects copied from earlier
# leaf/cpilot/front/slice caches; preserve its selections before filling gaps.
for label in ['slice-s-compose7','slice-s-compose6','slice-s-compose5','slice-s-compose4','slice-s-compose3','slice-s-compose2','slice-s-compose','front4','front2','cpilot','leaf']:
 src=b.parent/('codex-cx-'+label+'-cache-'+('20261027' if label=='leaf' else '20261028' if label in ['front4','front2','cpilot'] else '20261029'))
 if not src.exists():continue
 for p in src.rglob('*'):
  if p.is_file() and p.suffix in ['.olean','.lean']:
   rel=p.relative_to(src);dst=cache/rel
   if dst.exists():continue
   dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
   records.append(dict(source=str(p),destination=str(dst),sha256=sha(p)))
old=b.parent/'codex-cx-slice-s-compose7-20261029'
for n in ['S2W_run_host.py']:
 shutil.copy2(old/n,b/n);records.append(dict(source=str(old/n),destination=str(b/n),sha256=sha(b/n)))
s=b/'NEX_src'
assert not s.exists(),'setup is one-shot'
shutil.copytree(old/'NEU_src',s)
for n in ['NEU_contracts_applied.patch','NEU_oracle.patch']:
 patch=old/n
 if patch.read_text():subprocess.run(['git','apply','--reverse',str(patch)],cwd=s,check=True,capture_output=True)
# Existing pinned KMX and NED control modules remain unchanged, without NEU hooks.
manifest={str(p.relative_to(s)):sha(p) for p in s.rglob('*') if p.is_file()}
(b/'NEX_RUST_SHA256.json').write_text(json.dumps(manifest,indent=1))
(b/'NEX_objects').mkdir(exist_ok=True)
for p in (cache/'NEU_final_objects_20261104').rglob('*'):
 if p.is_file():
  dst=b/'NEX_objects'/p.relative_to(cache/'NEU_final_objects_20261104');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
(b/'NEX_HOST_PINS.json').write_text(json.dumps(dict(imports=records,source_manifest=manifest,admission=json.loads(q.read_text())),indent=1))
print(json.dumps(dict(imports=len(records),source_files=len(manifest),launcher_sha256=sha(b/'S2W_run_host.py'))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
(E/'NEX_SETUP.log').write_text(r.stdout+r.stderr)
print(r.stdout+r.stderr);assert r.returncode==0
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/NEX_HOST_PINS.json'],capture_output=True,text=True);assert r.returncode==0
(E/'NEX_HOST_PINS.json').write_text(r.stdout)
