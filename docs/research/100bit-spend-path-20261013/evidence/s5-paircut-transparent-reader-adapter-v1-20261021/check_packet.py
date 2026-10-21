#!/usr/bin/env python3
import hashlib,json,sys,subprocess
from pathlib import Path
p=Path(__file__).resolve().parent
m=json.loads((p/'manifest.json').read_text())
def h(f): return hashlib.sha256((p/f).read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1'
for mod in m['modules']:
 assert h(mod['source'])==mod['source_sha256']
assert h('dependencies/S5PairCutFieldCallbackV1.lean')==m['direct_import_source_map']['S5PairCutFieldCallbackV1']['source_sha256']
for mod in m['transitive_import_source_map'].values(): assert h(mod['source'])==mod['source_sha256']
expected={f['path'] for f in m['files']}
actual={q.relative_to(p).as_posix() for q in p.rglob('*') if q.is_file() and q.name not in {'manifest.json','SHA256SUMS'}}
assert actual==expected,(actual-expected,expected-actual)
for f in m['files']:
 q=p/f['path']; assert q.is_file() and h(f['path'])==f['sha256'] and q.stat().st_size==f['size_bytes'],f['path']
assert not list(p.rglob('*.olean')) and not list(p.rglob('*.llbc'))
assert 'actualReader_eq_checkedCallback' in (p/'evidence/target-lean.log').read_text()
assert 'propext' in (p/'evidence/target-lean.log').read_text()
subprocess.run([sys.executable,str(p/'extraction/check_reader_source.py')],check=True)
print('PASS:',m['packet'],len(m['files']),'files')
