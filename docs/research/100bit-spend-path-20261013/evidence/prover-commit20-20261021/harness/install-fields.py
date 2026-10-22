from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit20-20261021')
p=H/'src/crates/aspis-r1-cost-probe/src/r1_wire.rs'
s=p.read_text(); original=hashlib.sha256(s.encode()).hexdigest()
assert 'pub mod fields20' not in s
addition=(H/'harness/fields20.rs').read_text()
p.unlink();p.write_text(s+'\n'+addition)
(H/'fields20-binding.json').write_text(json.dumps(dict(base_revision='8f5d893d7',original_sha256=original,reference_sha256=hashlib.sha256(addition.encode()).hexdigest(),instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),production_changes=False,host_only_instrumentation=True),indent=2)+'\n')
