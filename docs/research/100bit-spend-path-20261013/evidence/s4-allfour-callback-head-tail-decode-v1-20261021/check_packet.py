#!/usr/bin/env python3
import hashlib, json, re, sys
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
for ent in m['files']:
    f=root/ent['path']
    if not f.is_file(): raise SystemExit(f"missing file: {ent['path']}")
    b=f.read_bytes()
    if len(b)!=ent['size_bytes'] or hashlib.sha256(b).hexdigest()!=ent['sha256']:
        raise SystemExit(f"file pin mismatch: {ent['path']}")
source=(root/m['modules'][0]['source']).read_text()
imports=set(re.findall(r'^import\s+(\S+)',source,re.M))
if imports != set(m['direct_import_source_map']):
    raise SystemExit(f"direct imports mismatch: source={sorted(imports)} map={sorted(m['direct_import_source_map'])}")
for name,ent in m['direct_import_source_map'].items():
    f=root/ent['source']
    if hashlib.sha256(f.read_bytes()).hexdigest()!=ent['source_sha256']:
        raise SystemExit(f"source pin mismatch: {name}")
for mod in m['modules']:
    rec=json.loads((root/mod['receipt']).read_text())
    if rec.get('exit_status')!=0: raise SystemExit(f"nonzero receipt: {mod['module']}")
    if rec.get('source_sha256', rec.get('source_sha256_at_launch'))!=mod['source_sha256']:
        raise SystemExit(f"receipt source pin mismatch: {mod['module']}")
    if rec.get('object_sha256') is not None and rec.get('object_sha256')!=mod['object_sha256']:
        raise SystemExit(f"receipt object pin mismatch: {mod['module']}")
print('PASS',m['packet'],len(m['files']),'files')
