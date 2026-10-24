"""Check the final focused audit's object inputs without replaying Lean."""
from pathlib import Path
import hashlib,json
h=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/stage3')
j=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
r=json.loads((h/'11288-input.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mismatches=[d['module'] for d in r['dependencies'] if sha(Path(d['resolved_object']))!=d['object_sha256']]
sources={p.stem:sha(p) for p in (j/'sources/R1Z').glob('ProverRwEffect*.lean')}
print(json.dumps(dict(audit_attempt=11288,source_revision=r['source_revision'],audit_source_sha256=r['source_sha256'],dependency_fingerprint=r['deps_fingerprint'],dependency_objects_checked=len(r['dependencies']),mismatches=mismatches,effect_source_sha256=sources,validation='Read-only hash check after the one focused audit; no Lean replay'),indent=2))
assert not mismatches
