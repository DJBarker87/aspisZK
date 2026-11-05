from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent; R=E.parent.parent
paths=subprocess.check_output(['git','ls-files'],text=True).splitlines()
G=json.loads((E.parent/'slice-s-retarget-20261104/NFY_SOURCE_GRAPH.json').read_text())
admitted={r['module'] for r in map(json.loads,(E.parent/'pool-retarget-20261105/NGK_LOADED_scan.jsonl').read_text().splitlines())}
P=json.loads((E.parent/'pool-retarget-20261105/NGK_PROVENANCE.json').read_text());reuse=P['module_owner'];rename=P['namespace_map']
# Include mappings deliberately absent from the Pool subset.
reuse.update(json.loads((E.parent/'slice-s-retarget-20261104/NFY_CANONICAL_REUSE.json').read_text()))
lookup={}
for p in paths:
 if p.endswith('.lean'):
  lookup.setdefault(Path(p).stem,[]).append(p)
def source(n):
 if n in G:return G[n]
 candidates=lookup.get(n.split('.')[-1],[])
 preferred=[p for p in candidates if p=='lean/'+n.replace('.','/')+'.lean']
 preferred+=sorted(candidates,key=lambda p:('/sources/' in p or re.search(r'/[A-Z]+_[LKE][0-9]+/',p) is not None,len(p),p))
 if not preferred:raise ValueError(('missing',n))
 p=preferred[0];s=subprocess.check_output(['git','show','HEAD:'+p],text=True)
 G[n]=dict(path=p,source=s,imports=re.findall(r'^import ([\w.]+)',s,re.M));return G[n]
seen=set();order=[];edges={}
def visit(n):
 if n in seen:return
 seen.add(n)
 if n in reuse or n in admitted:return
 r=source(n);edges[n]=r['imports']
 for d in r['imports']:visit(d)
 order.append(n)
for n in ['LPt_PreparedClaim','LPq_CarrierFacts']:visit(n)
(E/'NGU_SOURCE_GRAPH.json').write_text(json.dumps({n:G[n] for n in order},indent=1)+'\n')
(E/'NGU_DISCOVERY.json').write_text(json.dumps(dict(order=order,edges=edges,reuse={n:reuse[n] for n in seen if n in reuse},admitted=sorted(seen&admitted),namespace_map=rename),indent=1)+'\n')
print('new',len(order));print('\n'.join(order))
