from pathlib import Path
import json,subprocess,re,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
base=json.loads((E.parent/'slice-q-phase-20261104/NFN_SOURCE_GRAPH.json').read_text())
paths=subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines()
index={}
for p in paths:
 if '/sources/' in p or re.search(r'/[A-Z]+_L\d+/',p):continue
 n=Path(p).stem
 index.setdefault(n,[]).append(p)
graph={};missing=[]
def visit(n):
 if n in graph:return
 if n in base:r=base[n]
 else:
  ps=index.get(n,[])
  if '.' in n:
   ps=[p for p in paths if p.endswith(n.replace('.','/')+'.lean') and '/sources/' not in p]
  if not ps:missing.append(n);graph[n]={'imports':[],'missing':True};return
  ps.sort(key=lambda p:(not p.startswith('lean/'),len(p)))
  p=ps[0]
  src=Path(p).read_text() if Path(p).exists() else subprocess.check_output(['git','show','HEAD:'+p],text=True)
  r={'path':p,'source':src,'imports':[m for l in src.splitlines() if l.startswith('import ') for m in l[7:].split() if m!='all']}
 graph[n]=r
 for d in r['imports']:visit(d)
visit('NEV_AccumPacket')
# Full graph is retained once. Identify ALL paths to legacy Phase.
from functools import lru_cache
@lru_cache(None)
def bad(n):return n=='S1SemanticPhaseV1' or any(bad(d) for d in graph[n]['imports'])
order=[]
def ordervisit(n):
 if n in order or not bad(n):return
 for d in graph[n]['imports']:ordervisit(d)
 order.append(n)
ordervisit('NEV_AccumPacket')
reuse=json.loads((E.parent/'slice-q-phase-20261104/NFN_RETARGET_PROVENANCE.json').read_text())
(E/'NFS_SOURCE_GRAPH.json').write_text(json.dumps(graph,indent=1)+'\n')
(E/'NFS_DIAGNOSIS.json').write_text(json.dumps({'root':'NEV_AccumPacket','legacy_owner':'S1SemanticPhaseV1','affected_dependency_order':order,'NFN_reuse':{n:reuse['module_owner'][n] for n in order if n in reuse['module_owner']},'missing_sources':missing},indent=1)+'\n')
print(json.dumps({'affected':order,'reused':{n:reuse['module_owner'][n] for n in order if n in reuse['module_owner']},'missing':missing},indent=1))
