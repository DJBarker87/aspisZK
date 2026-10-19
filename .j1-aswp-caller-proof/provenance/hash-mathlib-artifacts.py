from pathlib import Path
import sys,json,hashlib,time
start=time.monotonic();mode=sys.argv[1];inp=Path(sys.argv[2]);data=json.loads(inp.read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(4*1024*1024),b''):h.update(b)
 return h.hexdigest()
roots=list(Path('/Users/dominic/ZK/AspisFormal/.lake/packages').iterdir()) if mode=='local' else []
rows={};total=0;missing=[]
for name,node in data['nodes'].items():
 if mode=='local':
  rel=name.replace('.','/')+'.lean';hits=[p for p in roots if (p/rel).is_file()]
  if len(hits)!=1:missing.append([name,'source_roots',list(map(str,hits))]);continue
  root=hits[0];src=root/rel;artbase=root/'.lake/build/lib/lean'/name.replace('.','/')
 else:src=Path(node['source']);artbase=None
 assert sha(src)==node['source_sha256'],name
 arts={}
 for ext,oldpath in node['artifact_paths'].items():
  p=Path(str(artbase)+ext) if mode=='local' else Path(oldpath)
  if not p.is_file():missing.append([name,ext,str(p)]);continue
  total+=p.stat().st_size;arts[ext]={'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
 rows[name]={'source':str(src),'source_sha256':node['source_sha256'],'artifacts':arts}
print(json.dumps({'scope':'Fresh streaming SHA-256 of every workspace artifact in the exact historical Mathlib import closure, with source SHA equality checked. No Lean or build.','mode':mode,'input_sha256':sha(inp),'wall_seconds':time.monotonic()-start,'artifact_bytes':total,'modules':len(rows),'artifact_count':sum(len(x['artifacts']) for x in rows.values()),'missing':missing,'nodes':rows},indent=2,sort_keys=True))
