from pathlib import Path
import json,gzip
P=Path(__file__).resolve().parent
m=json.loads((P/'manifest.json').read_text());keys={(x['ref'],x['path']) for x in m}
for name in ['independent-manifest9.json','supplement-manifest9.json']:
 for x in json.loads((P/name).read_text()):
  if (x['ref'],x['path']) not in keys:m.append(x);keys.add((x['ref'],x['path']))
(P/'manifest.json').write_text(json.dumps(m,indent=1)+'\n')
used={x['snapshot'] for x in m if x['snapshot'].startswith('objects/')};mapping={}
for path in used:
 f=P/path
 if f.suffix=='.txt':
  raw=f.read_bytes();g=Path(str(f)+'.gz');g.write_bytes(gzip.compress(raw,compresslevel=9,mtime=0));mapping[path]=path+'.gz';f.unlink()
for f in (P/'objects').iterdir():
 if 'objects/'+f.name not in used and 'objects/'+f.name not in mapping.values():f.unlink()
def fix(v):
 if isinstance(v,dict):
  for k,x in list(v.items()):v[k]=mapping.get(x,x) if k=='snapshot' and isinstance(x,str) else fix(x)
 elif isinstance(v,list):return [fix(x) for x in v]
 return v
for name in ['manifest.json','independent-manifest9.json','supplement-manifest9.json','definition-audit9.json']:
 f=P/name;f.write_text(json.dumps(fix(json.loads(f.read_text())),indent=1)+'\n')
print('Total payload bytes',sum(f.stat().st_size for f in P.rglob('*') if f.is_file()))
