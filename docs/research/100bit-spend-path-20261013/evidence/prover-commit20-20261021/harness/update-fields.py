from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit20-20261021')
p=H/'src/crates/aspis-r1-cost-probe/src/r1_wire.rs';s=p.read_text()
s=s[:s.index('// Owned state:')]+(H/'harness/fields20.rs').read_text()
p.write_text(s)
(H/'fields20-v2-binding.json').write_text(json.dumps(dict(instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reference_sha256=hashlib.sha256((H/'harness/fields20.rs').read_bytes()).hexdigest(),change='explicit Option match replaces ok_or only',host_only_instrumentation=True),indent=2)+'\n')
