#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for x in m['files']:
 p=r/x['path'];assert p.is_file() and p.stat().st_size==x['size_bytes'] and sha(p)==x['sha256'],x['path']
for x in m['modules']: assert sha(r/x['source'])==x['source_sha256']
for x in m['direct_import_source_map'].values(): assert sha(r/x['source'])==x['source_sha256']
for x in m['selected_transitive_owners'].values(): assert sha(r/x['source'])==x['source_sha256']
assert m['modules'][0]['object_sha256']=='f520d7964a62e21e464ad5f68ef8e4eed8080310b89056cdaee6ca3a0641faef'
assert m['modules'][0]['axioms']==['propext','Classical.choice','Quot.sound']
print('S4 N8 P6 canonical bridge packet checks passed')
