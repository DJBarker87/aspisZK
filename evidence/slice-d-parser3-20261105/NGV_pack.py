"""Deduplicate large archived inputs once by SHA; all bytes remain committed."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent;entries=[];assert not (E/'NGV_PACK.json').exists(),'Already packed; preserve the manifest';blobs=E/'NGV_blobs';blobs.mkdir(exist_ok=True)
for p in sorted(E.glob('NGV_*/sources/**/*')):
 if not p.is_file() or p.stat().st_size<=100000 or p.name.endswith('.REFERENCE.json'):continue
 data=p.read_bytes();sha=hashlib.sha256(data).hexdigest();name='NGV_blobs/'+sha+'.xz';target=E/name
 if target.exists():assert lzma.decompress(target.read_bytes())==data
 else:target.write_bytes(lzma.compress(data,preset=6))
 (E/(name+'.sha256')).write_text(sha+'  '+str(p.relative_to(E))+'\n')
 entry=dict(original=str(p.relative_to(E)),blob=name,sha256=sha,bytes=len(data));entries.append(entry)
 (E/(str(p.relative_to(E))+'.REFERENCE.json')).write_text(json.dumps(entry,indent=2)+'\n');p.unlink()
(E/'NGV_PACK.json').write_text(json.dumps(dict(entries=entries),indent=2)+'\n');print('Packed',len(entries),'large archived inputs into',len(set(e['blob']for e in entries)),'hash-addressed blobs')
