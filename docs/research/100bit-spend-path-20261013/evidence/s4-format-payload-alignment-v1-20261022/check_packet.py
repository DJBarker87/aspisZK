#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
pre=json.loads((root/'receipt/preflight.json').read_text())
run=json.loads((root/'receipt/receipt.json').read_text())
source=root/'sources/S4FormatPayloadAlignmentV1.lean'
assert sha(source)==pre['source_sha256']==run['source_sha256']
assert run['exit_status']==0 and run['object_sha256']=='9185d9149935479f1f2165e38410ec32861ddeb50162552882125b6f45a3e87b'
assert pre['source_revision']==run['revision_at_launch']=='942f5e3a556f0d20f3e5f113275b8a92c83767a1'
assert run['swaps']==0
log=(root/'receipt/lean.log').read_text()
assert "'AspisR1S4FormatPayloadAlignmentV1.payload_partitions' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
text=source.read_text()
assert 'theorem payload_partitions' in text and '#print axioms payload_partitions' in text
assert not re.search(r'^import\s+AspisR1S4FormatPayloadAlignmentV1\b',text,re.M)
assert not list(root.rglob('*.olean'))
for name,item in pre['direct_imports'].items():
 p=Path(item['path']); assert p.is_file() and sha(p)==item['sha256'],name
assert pre['profile_sha256']==sha(Path(pre['profile']))
print('S4 payload alignment packet: PASS')
