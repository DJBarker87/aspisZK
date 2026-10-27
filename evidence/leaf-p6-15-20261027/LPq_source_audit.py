"""Read-only freeze and local input audit; does not invoke a compiler."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent; frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
sha=lambda b:hashlib.sha256(b).hexdigest()
prior=json.loads(Path('evidence/leaf-p6-11-20261027/LPm_SOURCE_AUDIT.json').read_text())
files={};errors=[]
for name,pin in prior['files'].items():
 p=Path(name)
 if not p.is_file():errors.append([name,'missing']);continue
 actual=sha(p.read_bytes()); want=pin['frozen_sha256']
 files[name]=dict(bytes=p.stat().st_size,sha256=actual,frozen_sha256=want)
 if actual!=want:errors.append([name,'frozen mismatch'])
lock=sha(Path('Cargo.lock').read_bytes())
if lock!='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef':errors.append(['Cargo.lock','frozen mismatch'])
inputs=['evidence/leaf-p6-11-20261027/LPm_HANDOFF.md','evidence/leaf-p6-11-20261027/LPm_prepared_claim_LEAF.md','evidence/leaf-p6-11-20261027/LPm_checkpoint_LEAF.md','evidence/leaf-p6-11-20261027/LPm_harness.patch','evidence/leaf-p6-9-20261027/LPi_harness.patch','evidence/leaf-p6-6-20261027/LPf_harness.patch','evidence/sound-int2-20261025/HANDOFF.md','evidence/extraction-assoc17-20261027/XRy_HANDOFF.md','evidence/leaf-p6-12-20261027/LPn_DotClosed.lean']
input_pins={n:dict(bytes=Path(n).stat().st_size,sha256=sha(Path(n).read_bytes())) for n in inputs}
s=Path('crates/aspis-r1-cost-probe/src/verifier.rs').read_bytes()
body=s[s.index(b'fn prepared_claim<'):s.index(b'\nimpl Prepared {')]
report=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_revision=frozen,source_tree_dirty=True,files=files,errors=errors,lock_sha256=lock,inputs=input_pins,prepared_claim_body=dict(sha256=sha(body),bytes=len(body),start_line=53,end_line=70),native_scopes_launched=0,lean_attempts_launched=0,validation='static only, no source-to-model or source-to-ELF closure')
(E/'LPq_SOURCE_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(files=len(files),errors=errors,body=report['prepared_claim_body'])))
assert not errors
