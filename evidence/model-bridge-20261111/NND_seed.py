from pathlib import Path
import json,lzma,hashlib,shutil
B=Path.cwd(); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
M=Path('/home/dombarker/project-offloads/codex-cx-tx2-entry5-20261110/NMN_CLOSURE_PINS.json.xz')
rows=json.loads(lzma.decompress(M.read_bytes()));out=B/'NND_seed';out.mkdir(exist_ok=True);imported=[]
for r in rows:
 p=Path(r['path']);assert sha(p)==r['sha256'],str(p)
 suffix=''.join(p.suffixes);rel=r['module'].replace('.','/')+suffix;q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==r['sha256'],('duplicate conflict',rel)
 else:shutil.copy2(p,q)
 assert sha(q)==r['sha256']
 imported.append(dict(r,destination=str(q)))
# ledger24 export must lead and be copied explicitly.
m=json.loads((B/'NND_NLX_EXPORT.json').read_text())
for r in m['files']:
 p=Path(r['path']);assert sha(p)==r['sha256'];q=B/'NND_NLX_seed'/p.name;q.parent.mkdir(exist_ok=True)
 if q.exists():assert sha(q)==r['sha256']
 else:shutil.copy2(p,q)
 imported.append(dict(r,destination=str(q)))
raw=json.dumps(dict(predecessor_manifest=str(M),predecessor_sha256=sha(M),files=imported)).encode()
(B/'NND_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(B/'NND_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(files=len(imported),bytes=sum(x['bytes'] for x in imported),free=shutil.disk_usage(B).free)))
