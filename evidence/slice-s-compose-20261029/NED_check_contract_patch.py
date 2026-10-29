"""Read-only cfg-only harness patch validation; Rust lives only in scratch."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;s=(E/'NED_contract_controls.patch').read_text();shape=json.loads((E/'NED_CONTRACT_SHAPES.json').read_text())
paths=re.findall(r'^\+\+\+ b/(.+)$',s,re.M)
assert paths==['crates/aspis-statement/src/lib.rs','crates/aspis-statement/src/NED_controls.rs']
start=s.index('+++ b/crates/aspis-statement/src/NED_controls.rs')
body=''.join(line[1:] for line in s[start:].splitlines(True) if line.startswith('+') and not line.startswith('+++'))
assert hashlib.sha256(body.encode()).hexdigest()==shape['source_sha256']
assert 'Option<fn' not in body and 'fn(' not in body
assert set(re.findall(r'^fn (\w+)\(\)',body,re.M))=={'exact_contract','inverted_contract','weak_contract','weak_real','weak_unimplied','frame_positive','frame_violation'}
assert 'type Reply = Result<[u8;216],E>;' in body
print('validated exact sum/fixed-array controls patch; no native credit')
