from NND_transport import *
import base64,hashlib,lzma
records=[]
for p in sorted(E.glob('NND_L*/NND_RAW_AUDIT.json')):records.extend(json.loads(p.read_text())['archives'])
assert len(records)==322,len(records)
names=[r['path'] for r in records]
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});names=json.loads({json.dumps(names)!r})
print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in names}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for row in records:
 z=base64.b64decode(out[row['path']]);assert hashlib.sha256(z).hexdigest()==row['archive_sha256']
 raw=lzma.decompress(z);assert hashlib.sha256(raw).hexdigest()==row['sha256'] and len(raw)==row['bytes']
 p=E/row['path'];p.parent.mkdir(exist_ok=True);p.write_bytes(z);p.with_suffix('.sha256').write_text(row['sha256']+'\n')
(E/'NND_RAW_ARCHIVES.json').write_text(json.dumps(records,indent=1)+'\n')
print(json.dumps({'raw_graphs':len(records),'compressed_bytes':sum((E/r['path']).stat().st_size for r in records),'all_hashes_verified':True}))
