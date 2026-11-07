"""Explicit inherited module inventory, split into bounded hash batches."""
from pathlib import Path
import json,hashlib,lzma,sys
B=Path.cwd();i=int(sys.argv[1]);assert i in range(3)
sha=lambda b:hashlib.sha256(b).hexdigest()
if i==0:
 root=B.parent/'codex-cx-entry-wrap-20261111/NMW_CLOSURE_PINS.json.xz'
 raw=root.read_bytes();expected=json.loads((B/'NNF_PREDECESSOR_PIN.json').read_text())
 assert sha(raw)==expected['archive_sha256'],'predecessor inventory changed'
 raw=lzma.decompress(raw);assert sha(raw)==expected['uncompressed_sha256']
 old=json.loads(raw);env=json.loads((B/'NNF_ENV.json').read_text());roots=env['LEAN_PATH'].split(':')
 assert roots[4:]==old['LEAN_PATH'].split(':')[2:],'unexpected inherited path change'
 selected={}
 for row in old['selected_objects']:
  suffix=next(s for s in ['.olean.private','.olean.server','.olean','.ir'] if row['path'].endswith(s))
  rel=row['module'].replace('.','/')+suffix
  p=next((Path(r)/rel for r in roots[:4] if (Path(r)/rel).is_file()),Path(row['path']))
  selected[rel]={'path':str(p),'sha256':row['sha256'],'bytes':row['bytes']}
 # Only new prefixes are enumerated (flat, small owned export directories).
 for r in reversed(roots[:4]):
  for p in Path(r).glob('*'):
   if p.is_file() and p.name.endswith(('.olean','.olean.private','.olean.server','.ir')):
    selected[p.name]={'path':str(p),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
 x={'inventory':'exact predecessor first-hit module inventory plus own/RSL additions; no recursive cache scan','LEAN_PATH':env['LEAN_PATH'],'selected':selected,'predecessor':expected}
 raw=json.dumps(x,sort_keys=True).encode();(B/'NNF_PIN_SELECTION.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NNF_PIN_SELECTION.json.sha256').write_text(sha(raw)+'\n')
raw=lzma.decompress((B/'NNF_PIN_SELECTION.json.xz').read_bytes());h=(B/'NNF_PIN_SELECTION.json.sha256').read_text().strip();assert sha(raw)==h
rows=sorted(json.loads(raw)['selected'].items());n=len(rows);start=n*i//3;end=n*(i+1)//3
for j,(rel,row) in enumerate(rows[start:end],start):
 p=Path(row['path']);assert p.stat().st_size==row['bytes'] and sha(p.read_bytes())==row['sha256'],('OBJECT DRIFT',rel,str(p))
 if (j-start)%2000==0:print(json.dumps({'batch':i,'checked':j-start,'total':end-start}),flush=True)
x={'batch':i,'selection_sha256':h,'start':start,'end':end,'total':n,'verified':True,'checked_rows_sha256':sha(json.dumps(rows[start:end],sort_keys=True).encode())}
(B/f'NNF_PIN_BATCH_{i}.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x),flush=True)
