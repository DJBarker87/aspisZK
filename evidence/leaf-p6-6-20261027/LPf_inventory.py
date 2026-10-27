"""Read-only scratch/frozen inventory and additive-overlay audit."""
from pathlib import Path
import json,subprocess,hashlib,tarfile,io
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-6-20261027/LPf_src'
frozen={}
tar=subprocess.check_output(['git','archive',F,'crates','programs','Cargo.lock','Cargo.toml'])
tf=tarfile.open(fileobj=io.BytesIO(tar))
for m in tf:
 if m.isfile():
  data=tf.extractfile(m).read();frozen[m.name]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
code='''from pathlib import Path
import hashlib,json
b=Path(%r);paths=[b/'Cargo.lock',b/'Cargo.toml']
for root in ['crates','programs']:paths.extend(p for p in (b/root).rglob('*') if p.is_file())
print(json.dumps({str(p.relative_to(b)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in paths}))
'''%B
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True);actual=json.loads(r.stdout)
allowed={'crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/fast_pairing.rs','crates/aspis-r1-cost-probe/src/verifier.rs'}
missing=sorted(set(frozen)-set(actual));extras=sorted(set(actual)-set(frozen));changed=sorted(k for k in frozen.keys()&actual.keys() if frozen[k]!=actual[k]);errors=[]
if missing:errors.append(['missing',missing])
if set(changed)-allowed:errors.append(['changed',changed])
if any(not Path(k).name.startswith('LPf_') for k in extras):errors.append(['extra',extras])
patches={}
for p in E.glob('LPf_K*/LPf_harness.patch'):
 removed=[l for l in p.read_text().splitlines() if l.startswith('-') and not l.startswith('---')]
 if removed:errors.append(['nonadditive overlay',str(p),removed])
 patches[str(p.relative_to(E))]=hashlib.sha256(p.read_bytes()).hexdigest()
(E/'LPf_frozen_native_manifest.json').write_text(json.dumps(frozen,indent=2)+'\n')
(E/'LPf_scratch_native_manifest.json').write_text(json.dumps(actual,indent=2)+'\n')
(E/'LPf_SOURCE_AUDIT.json').write_text(json.dumps(dict(frozen_revision=F,frozen_files=len(frozen),actual_files=len(actual),missing=missing,changed=changed,extra=extras,patches=patches,errors=errors),indent=2)+'\n')
assert not errors,errors
print('native source inventory PASS',len(frozen),len(actual),flush=True)
