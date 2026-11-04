from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code=r'''
from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose10-20261029');b.mkdir(exist_ok=True)
q=b/'NFD_SETUP-reservation.json'
with (b/'NFD_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
print((b/'NFD_SETUP-barrier.log').read_text(),flush=True)
if r.returncode!=0 or json.loads(q.read_text()).get('allowed') is not True:sys.exit(78)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cache=b.parent/'codex-cx-slice-s-compose10-cache-20261029';cache.mkdir(exist_ok=True);records=[]
for label in ['slice-s-compose9','slice-s-compose8','slice-s-compose7','slice-s-compose6','slice-s-compose5','slice-s-compose4','slice-s-compose3','slice-s-compose2','slice-s-compose','front4','front2','cpilot','leaf']:
 src=b.parent/('codex-cx-'+label+'-cache-'+('20261027' if label=='leaf' else '20261028' if label in ['front4','front2','cpilot'] else '20261029'))
 if not src.exists():continue
 for p in src.rglob('*'):
  if p.is_file() and p.suffix in ['.olean','.lean']:
   dst=cache/p.relative_to(src)
   if dst.exists():continue
   dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst);records.append(dict(source=str(p),destination=str(dst),sha256=sha(p)))
old=b.parent/'codex-cx-slice-s-compose9-20261029'
shutil.copy2(old/'S2W_run_host.py',b/'S2W_run_host.py')
s=b/'NFD_src';assert not s.exists(),'one shot setup'
shutil.copytree(old/'NEY_src',s)
for n in ['NEY_contracts_applied.patch','NEY_oracle.patch']:
 if (old/n).read_text():subprocess.run(['git','apply','--reverse',str(old/n)],cwd=s,check=True,capture_output=True)
# Verify the frozen lock is copied, not resolved anew.
assert sha(s/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
manifest={str(p.relative_to(s)):sha(p) for p in s.rglob('*') if p.is_file()}
(b/'NFD_RUST_SHA256.json').write_text(json.dumps(manifest,indent=1))
(b/'NFD_objects').mkdir(exist_ok=True)
(b/'NFD_HOST_PINS.json').write_text(json.dumps(dict(imports=records,source_manifest=manifest,admission=json.loads(q.read_text()),launcher_sha256=sha(b/'S2W_run_host.py')),indent=1))
print(json.dumps(dict(imports=len(records),source_files=len(manifest))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NFD_SETUP.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr,flush=True)
if r.returncode:raise SystemExit(r.returncode)
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-slice-s-compose10-20261029/NFD_HOST_PINS.json'],capture_output=True,text=True)
assert r.returncode==0,r.stderr
(E/'NFD_HOST_PINS.json').write_text(r.stdout)
