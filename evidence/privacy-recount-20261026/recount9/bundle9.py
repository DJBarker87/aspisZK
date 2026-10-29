from pathlib import Path
import gzip,json
P=Path(__file__).resolve().parent;small=[f for f in (P/'objects').glob('*.txt.gz') if f.stat().st_size<2048];mapping={}
for start in range(0,len(small),1000):
 group=small[start:start+1000];name=f'objects/text-bundle-{start//1000:03d}.json.gz';data={}
 for f in group:
  key=f.name.split('.')[0];data[key]=gzip.decompress(f.read_bytes()).decode('utf8');mapping['objects/'+f.name]=(name,key)
 (P/name).write_bytes(gzip.compress(json.dumps(data,ensure_ascii=False,separators=(',',':')).encode(),compresslevel=9,mtime=0))
 for f in group:f.unlink()
def fix(v):
 if isinstance(v,dict):
  old=v.get('snapshot')
  if old in mapping:v['snapshot'],v['snapshot_key']=mapping[old]
  for k,x in v.items():
   if isinstance(x,(dict,list)):fix(x)
 elif isinstance(v,list):
  for x in v:fix(x)
for name in ['manifest.json','independent-manifest9.json','supplement-manifest9.json','definition-audit9.json']:
 f=P/name;x=json.loads(f.read_text());fix(x);f.write_text(json.dumps(x,indent=1)+'\n')
print('Bundled',len(small),'small text snapshots in',len(list((P/'objects').glob('text-bundle*'))),'JSON text bundles')
