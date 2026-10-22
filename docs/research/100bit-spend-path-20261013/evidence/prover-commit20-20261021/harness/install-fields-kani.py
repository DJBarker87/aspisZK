from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit20-20261021')
p=H/'src/crates/aspis-r1-cost-probe/src/r1_wire.rs';s=p.read_text();assert 'mod fields_kani20' not in s
s+='\n'+(H/'harness/fields-kani20.rs').read_text();p.write_text(s)
(H/'fields-kani20-binding.json').write_text(json.dumps(dict(instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),production_validator_unchanged=True,host_only_instrumentation=True),indent=2)+'\n')
