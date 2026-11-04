"""Pack lossless evidence text into small JSON/xz shards; never build objects."""
import json,gzip,lzma,hashlib,base64
from pathlib import Path
P=Path(__file__).resolve().parent;m=json.loads((P/'manifest.json').read_text());unique={x['sha256']:x for x in m}
(P/'bundles').mkdir(exist_ok=True);mapping={};batch={};size=0;count=0
# Keep adjacent evidence paths together to share the xz dictionary.
def flush():
 global batch,size,count
 if not batch:return
 raw=json.dumps(batch,separators=(',',':'),ensure_ascii=False).encode();name=f'bundles/sources-{count:03}.json.xz'
 packed=lzma.compress(raw,preset=6);assert len(packed)<20*1024*1024
 (P/name).write_bytes(packed);(P/(name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
 for h in batch:mapping[h]={'snapshot':name,'snapshot_key':h,'snapshot_encoding':'json-record'}
 batch={};size=0;count+=1
for h,x in sorted(unique.items(),key=lambda q:(q[1]['ref'],q[1]['path'])):
 raw=gzip.decompress((P/x['snapshot']).read_bytes());assert hashlib.sha256(raw).hexdigest()==h
 if size+len(raw)>16*1024*1024:flush()
 try:val={'encoding':'utf8','data':raw.decode()}
 except UnicodeDecodeError:val={'encoding':'base64','data':base64.b64encode(raw).decode()}
 batch[h]=val;size+=len(raw)
flush()
# Update all source-witness JSONs, including the duplicated definition descriptors.
def walk(x):
 if isinstance(x,dict):
  if x.get('sha256') in mapping and str(x.get('snapshot','')).startswith('objects/'):
   x.update(mapping[x['sha256']])
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
for f in P.glob('*.json'):
 x=json.loads(f.read_text());walk(x)
 if f.name in ['rows11.json']:
  f.write_text('[\n'+',\n'.join(json.dumps(r,separators=(',',':')) for r in x)+'\n]\n')
 elif f.name in ['definition-audit11.json','import-closures11.json']:
  f.write_text(json.dumps(x,separators=(',',':'))+'\n')
 else:f.write_text(json.dumps(x,indent=1)+'\n')
# Verify every member before removing only this task's duplicate loose snapshots.
for name in sorted({v['snapshot'] for v in mapping.values()}):
 a=json.loads(lzma.decompress((P/name).read_bytes()))
 for h,v in a.items():
  raw=v['data'].encode() if v['encoding']=='utf8' else base64.b64decode(v['data'])
  assert hashlib.sha256(raw).hexdigest()==h
for f in (P/'objects').glob('*.gz'):f.unlink()
(P/'objects').rmdir()
print('Packed',len(mapping),'unique byte snapshots into',count,'JSON/xz shards;',sum(f.stat().st_size for f in P.rglob('*') if f.is_file()),'bytes total')
