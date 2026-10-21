from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit20-20261021')
p=H/'src/crates/aspis-r1-cost-probe/src/sim.rs';s=p.read_text()
assert 'mod table20' not in s
needle='if let Some(prev)=t.0.insert(concat(parts),self.answer) { if prev!=self.answer {t.1=true;} }'
assert needle in s
addition=(H/'harness/table20.rs').read_text()
p.unlink();p.write_text(s+'\n'+addition)
(H/'table20-binding.json').write_text(json.dumps(dict(source_fragment=needle,source_fragment_sha256=hashlib.sha256(needle.encode()).hexdigest(),instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reference_sha256=hashlib.sha256(addition.encode()).hexdigest(),boundary='Table::insert return value; per-entry collision branch only; not BTreeMap transport',host_only_instrumentation=True),indent=2)+'\n')
