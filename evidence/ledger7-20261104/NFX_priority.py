"""Restore the coherent SInt2 precedence before legacy fallback cache objects."""
from pathlib import Path
import json,lzma,os,hashlib
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-ledger7-20261104';C=P/'codex-cx-ledger7-cache-20261104';D=C/'NFX_priority';D.mkdir(exist_ok=True)
m=json.loads(lzma.decompress((B/'NFX_CACHE_IMPORTS.json.xz').read_bytes()));early=m['roots'][:m['roots'].index(str(P/'codex-cx-slice-q-accum-cache-20261104/NEV_exports_20261104'))]
rows=[]
for x in m['selected']:
 src=Path(x['source']);base=next((Path(r) for r in early if src.is_relative_to(r) and '/' not in str(src.relative_to(r)).strip('/')),None)
 # Namespace directories in known early export roots are also priority.
 if base is None:base=next((Path(r) for r in early if ('exports' in Path(r).name or 'objects' in Path(r).name or 'view' in Path(r).name) and src.is_relative_to(r)),None)
 is_s=src.name.startswith(('NEM_','NEQ_','NEU_','NEX_','NEY_','NFD_','NFH_','NFJ_'))
 if base is None and not is_s:continue
 own=Path(x['destination']);rel=own.relative_to(C);dest=D/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists():os.link(own,dest)
 rows.append(dict(path=str(dest),sha256=x['sha256'],source=x['source']))
raw=json.dumps(dict(priority=rows,reason='Match NFS/SInt2 lookup order: priority exports, SInt2 root/objects, fallback cache; previous flattened fallback preceded SInt2'),sort_keys=True).encode();(B/'NFX_PRIORITY_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NFX_PRIORITY_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');print(len(rows))
