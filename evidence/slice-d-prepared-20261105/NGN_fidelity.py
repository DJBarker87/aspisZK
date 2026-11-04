"""Compare all frozen shipped-source bytes to the private scratch overlay."""
from pathlib import Path
import subprocess,json,hashlib,tarfile,io
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';B='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-20261105'
data=subprocess.check_output(['git','archive',F,'Cargo.toml','Cargo.lock','crates','programs'],cwd=R);expected={}
with tarfile.open(fileobj=io.BytesIO(data)) as tar:
 for m in tar:
  if m.isfile():expected[m.name]=hashlib.sha256(tar.extractfile(m).read()).hexdigest()
(E/'NGN_FROZEN_FILE_PINS.json').write_text(json.dumps(expected,indent=1)+'\n')
overrides=json.loads((E/'NGN_SOURCE_PINS.json').read_text());code='''from pathlib import Path
import json,hashlib
s=Path(B)/'NGN_src';actual=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();errors=[]
for n,h in expected.items():
 if not (s/n).is_file() or actual(s/n)!=overrides.get(n,h):errors.append(n)
extra=[str(p.relative_to(s)) for d in ['crates','programs'] for p in (s/d).rglob('*') if p.is_file() and str(p.relative_to(s)) not in expected and str(p.relative_to(s)) not in overrides]
for n,h in overrides.items():
 if actual(s/n)!=h:errors.append(n)
print(json.dumps(dict(frozen_revision=F,files=len(expected),overrides=overrides,errors=errors,unexpected_files=extra,cargo_lock=actual(s/'Cargo.lock'),shipped_repository_changed=False)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nF='+repr(F)+'\nexpected='+repr(expected)+'\noverrides='+repr(overrides)+'\n'+code,text=True,capture_output=True);(E/'NGN_FIDELITY_TRANSPORT.log').write_text(r.stderr);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);assert not x['errors'] and not x['unexpected_files'],x
assert not subprocess.check_output(['git','diff',F,'--name-only','--','crates','programs'],cwd=R).strip()
assert not subprocess.check_output(['git','status','--porcelain','--','crates','programs'],cwd=R).strip()
(E/'NGN_SOURCE_FIDELITY.json').write_text(json.dumps(x,indent=1)+'\n');print('frozen source fidelity:',x['files'],'files, exact cfg-only scratch overlay')
