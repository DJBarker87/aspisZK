"""Read retained denial pins only; no new admission or build."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;O=D/'packet/rust001'
r=json.loads((O/'preflight.json').read_text())
base=str(D)+'/'
selected={p[len(base):]:h for p,h in r['source_sha256'].items() if p.startswith(base) and '/vendor/' not in p}
large=[dict(path=str(p),size_bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in [O/'preflight.json',O/'receipt.json']]
print(json.dumps(dict(command=['python3',str(D/'pin-assessment.py')],preflight_source_revision=r['source_revision'],job_source_pins_at_denial=selected,all_pin_count=len(r['source_sha256']),dependency_fingerprint=r['dependency_fingerprint'],oversized_json=large,compiler_invocations=0,go_exists=(O/'admission-barrier.json').exists(),target_started=(O/'target-started.json').exists(),assessment='Denied snapshot only; old base marker plus exact job-file hashes, including uncommitted source preparation completion. Not a new source identity gate or validation of later final harness.'),indent=2))
