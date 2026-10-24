#!/usr/bin/env python3
"""Recover only pinned proof objects into a private ephemeral warm cache.
No compiled object is part of the source-only evidence packet.
"""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]; B=R/'docs/research/100bit-spend-path-20261013'
manifest=B/'evidence/actual-decode-k-main-canonicality-20261019/manifest.json'
m=json.loads(manifest.read_text()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cache=Path('/tmp/s126-decoder-canonical-20261024-objects');cache.mkdir(exist_ok=True)
host='dombarker@100.108.41.90'; remote='/home/dombarker/project-offloads/terminal-v4-begin-mu-canonical-v1-20261019/prebuilt'
rows=[]
for row in m['modules']:
 n=row['module']
 if not(n.startswith('AspisR1DecodeK') and '.' not in n):continue
 source=B/'lean/extracted-decode-k-canonicality-20261018'/(n+'.lean')
 assert sha(source)==row['source_sha256'],n
 p=cache/(n+'.olean')
 if not p.exists():subprocess.run(['scp','-q',host+':'+remote+'/'+n+'.olean',str(p)],check=True)
 assert sha(p)==row['object_sha256'],n
 rows.append(dict(module=n,source=str(source.relative_to(R)),source_sha256=sha(source),object_sha256=sha(p),ephemeral_object=str(p),producer_receipt=str((manifest.parent/row['receipt']).relative_to(R)),remote_object=remote+'/'+n+'.olean'))
E=B/'evidence/s126-current-caller-20261021/s1-round-canonical-cache-20261024';E.mkdir(exist_ok=True)
(E/'provenance.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',manifest=str(manifest.relative_to(R)),manifest_sha256=sha(manifest),modules=rows,qualification='Reused exact producer objects with source/receipt checks; compiled files exist only in ephemeral cache, not this packet.'),indent=2)+'\n')
path=Path('/tmp/s126-semantic-effect-top-path-20261024.txt').read_text().strip()
Path('/tmp/s126-round-canonical-path-20261024.txt').write_text(str(cache)+':'+path+'\n')
print(json.dumps(dict(recovered=len(rows),cache=str(cache))))
