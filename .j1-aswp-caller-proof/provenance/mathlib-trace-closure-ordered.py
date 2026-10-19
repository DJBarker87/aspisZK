"""Pure read/hash reproduction of Lake4.32 legacy import aggregate; no build."""
from pathlib import Path
import hashlib,json,importlib.util,re
B=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015')
sp=importlib.util.spec_from_file_location('runner',B/'extracted/j1-r17-build-extracted-v2.py');r=importlib.util.module_from_spec(sp);sp.loader.exec_module(r)
packages=json.loads((B/'dependency-cache-pins.json').read_text());roots=[Path(p['path']) for p in packages]
mask=(1<<64)-1
def mix(h,k):
 m=0xc6a4a7935bd1e995;k=(k*m)&mask;k^=k>>47;k^=m;return ((h^k)*m)&mask
rows={};external=set();active=set()
def visit(n):
 if n in rows:return rows[n]
 hits=[p for p in roots if (p/(n.replace('.','/')+'.lean')).is_file()]
 if not hits:external.add(n);return None
 assert len(hits)==1,(n,hits)
 assert n not in active,n;active.add(n);p=hits[0];source=p/(n.replace('.','/')+'.lean');tr=p/'.lake/build/lib/lean'/(n.replace('.','/')+'.trace');t=json.loads(tr.read_text());out=t['outputs']
 deps=[]
 for line in r.uncomment(source.read_text()).splitlines():
  line=line.strip()
  if not line or line in ['module','prelude']:continue
  mt=re.match(r'^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)$',line)
  if not mt:break
  deps.extend(mt[1].split())
 h=1723;used=[]
 for dep in deps:
  d=visit(dep)
  if d:
   h=mix(mix(h,int(d['legacy_hash'],16)),int(d['all_arts_hash'],16));used.append(dep)
 art={}
 for f in out['o']:art['.'+f.split('.',1)[1]]=f.split('.',1)[0]
 if out.get('r'):art['.ir']=out['r'].split('.',1)[0]
 selected=['.olean','.ir','.olean.server','.olean.private'] if out.get('m',False) else ['.olean'];a=1723
 for ext in selected:a=mix(a,int(art[ext],16))
 row={'source':str(source),'source_sha256':r.sha(source),'trace':str(tr),'trace_sha256':r.sha(tr),'imports':used,'legacy_hash':f'{h:016x}','all_arts_hash':f'{a:016x}','module_system':out.get('m',False),'artifact_lake_hashes':{x:art[x] for x in selected},'artifact_paths':{x:str(tr.with_suffix(x)) for x in selected}}
 rows[n]=row;active.remove(n);return row
v=visit('Mathlib');print(json.dumps({'scope':'Reproduced aggregates from actual pinned source headers and retained Lake trace artifact hashes. Per-transitive-object bytes are not newly rehashed here; direct Mathlib artifacts separately SHA-compared local/host.', 'expected_legacy':'693e25ff4498b2e4','expected_all_arts':'f90ecd83c52e54ec','computed_root':v,'legacy_matches':v['legacy_hash']=='693e25ff4498b2e4','all_arts_matches':v['all_arts_hash']=='f90ecd83c52e54ec','module_count':len(rows),'builtin_imports_not_in_workspace':sorted(external),'nodes':rows},indent=2,sort_keys=True))
