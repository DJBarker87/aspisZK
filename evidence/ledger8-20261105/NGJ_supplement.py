from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent;P=E.parent
files=[]
for r in json.loads((P/'pool-retdata3-20261104/NFV_HOST_PINS.json').read_text())['imports']:
 p=r['destination'];root='/home/dombarker/project-offloads/codex-cx-pool-retdata3-cache-20261104/'
 if p.startswith(root) and any(p.endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):files.append(dict(source=p,relative='NGJ_pool_fallback/'+p[len(root):],sha256=r['sha256'],bytes=r['size']))
# NFQ imports are needed by NFT/NFU; use their byte-pinned retained imports.
for folder,pre in [('slice-d-check-20261104','NFU'),('slice-d-field-20261104','NFT')]:
 d=json.loads(lzma.decompress((P/folder/(pre+'_CACHE_IMPORTS.json.xz')).read_bytes()))
 (E/(pre+'_schema.txt')).write_text(str(type(d))+' '+str(list(d)[:5])[:600])
raw=json.dumps(files).encode();(E/'NGJ_POOL_SEED.json.xz').write_bytes(lzma.compress(raw));(E/'NGJ_POOL_SEED.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
s=(E/'NGJ_seed.py').read_text().replace('NGJ_SEED_INPUTS','NGJ_POOL_SEED').replace('NGJ_CACHE_IMPORTS','NGJ_POOL_CACHE_IMPORTS').replace('NGJ_SEED_RESERVATION','NGJ_POOL_SEED_RESERVATION').replace('NGJ_SEED_TRANSPORT','NGJ_POOL_SEED_TRANSPORT')
(E/'NGJ_pool_seed.py').write_text(s)
print(len(files),sum(r['bytes'] for r in files))
