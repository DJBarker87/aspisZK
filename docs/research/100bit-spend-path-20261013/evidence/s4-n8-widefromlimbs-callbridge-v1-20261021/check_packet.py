#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent
m=json.loads((r/'manifest.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f in m['files']:
 p=r/f['path']; assert p.is_file() and p.stat().st_size==f['size_bytes'] and sha(p)==f['sha256'],f['path']
for x in m['modules']:
 assert sha(r/x['source'])==x['source_sha256']
for x in m['direct_import_source_map'].values(): assert sha(r/x['source'])==x['source_sha256']
for x in m['selected_transitive_owners'].values(): assert sha(r/x['source'])==x['source_sha256']
assert m['modules'][0]['object_sha256']=='2d9309aaf0955bcbbb75538c9368daf0e9d4229d7e6394aa18e8241a2636c98b'
assert m['modules'][0]['axioms']==['propext','Classical.choice','Quot.sound']
assert m['selected_transitive_owners']['Aeneas.Std.Core.Fmt']['object_sha256']=='63b8efa3940faa81bb26f1b6ea140b2d6b81c1f1155b3fafa0544f6e1e82b9fc'
print('S4 N8 wideFromLimbs call-bridge packet checks passed')
