#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
root=Path(__file__).parent
manifest=json.loads((root/'manifest.json').read_text())
source=root/manifest['source']
assert hashlib.sha256(source.read_bytes()).hexdigest()==manifest['source_sha256']
receipt=json.loads((root/manifest['attempt']).read_text())
assert receipt['exit_status']==0 and receipt['swaps']==0
assert receipt['source_sha256']==manifest['source_sha256']
assert receipt['object_sha256']==manifest['object_sha256']
assert receipt['axioms']==manifest['axioms']
assert (root/'owner-pins.json').is_file()
assert 'readerE ops.raw' in source.read_text()
assert 'successful_fields' in source.read_text()
assert 'readerE_success_canonical' in source.read_text()
print('PASS s4 resume gamma actual canonical packet')
