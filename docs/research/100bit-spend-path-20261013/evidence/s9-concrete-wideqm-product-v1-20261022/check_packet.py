#!/usr/bin/env python3
import hashlib,json,pathlib
root=pathlib.Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['status'].startswith('source-only')
p=m['proof']; src=root/p['source']; assert hashlib.sha256(src.read_bytes()).hexdigest()==p['source_sha256']
assert p['exit_code']==0 and p['swap_bytes']==0 and p['axioms']==['propext','Classical.choice','Quot.sound']
obj=pathlib.Path(p['object_external_path']); assert obj.is_file() and hashlib.sha256(obj.read_bytes()).hexdigest()==p['object_sha256']
for o in m['selected_external_owners'].values():
 q=pathlib.Path(o['path']); assert q.is_file() and hashlib.sha256(q.read_bytes()).hexdigest()==o['sha256']
for s in m['selected_external_sources'].values():
 q=pathlib.Path('/Users/dominic/ZK')/s['path']; assert q.is_file() and hashlib.sha256(q.read_bytes()).hexdigest()==s['sha256']
c=json.loads((root/m['import_closure']['path']).read_text()); assert c['modules']==m['import_closure']['modules'] and not c['missing']
assert not list(root.rglob('*.olean'))
files=sorted(str(q.relative_to(root)) for q in root.rglob('*') if q.is_file() and q.name!='SHA256SUMS')
lines=(root/'SHA256SUMS').read_text().splitlines(); assert sorted(x.split('  ',1)[1] for x in lines)==files
for line in lines:
 h,n=line.split('  ',1); assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h
print('PASS')
