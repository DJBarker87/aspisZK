"""Compress completed reachable sets without changing their bytes."""
import hashlib,json,lzma
from pathlib import Path
B=Path(__file__).resolve().parent
rows={}
for p in B.glob('NEP_*_REACHABLE.txt'):
 raw=p.read_bytes();out=p.with_name(p.name+'.xz');out.write_bytes(lzma.compress(raw));digest=hashlib.sha256(raw).hexdigest();p.with_name(p.name+'.sha256').write_text(digest+'\n')
 rows[p.name]={'file':out.name,'sha256':digest,'count':len(raw.decode().splitlines())}
(B/'NEP_VISITED.json').write_text(json.dumps(rows,indent=2)+'\n')
