from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit20-20261021')
p=H/'src/crates/aspis-r1-cost-probe/src/r1_wire.rs';s=p.read_text();assert 'pub mod semantic20' not in s
addition=(H/'harness/semantic20.rs').read_text();p.write_text(s+'\n'+addition)
(H/'semantic20-binding.json').write_text(json.dumps(dict(instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reference_sha256=hashlib.sha256(addition.encode()).hexdigest(),source_methods=['row_shape','sample_block_validated','qm31_sample'],host_only_instrumentation=True),indent=2)+'\n')
