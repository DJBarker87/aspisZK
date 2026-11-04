"""Resolve immutable committed sources for unadmitted modules, no host/prover work."""
from pathlib import Path
import subprocess,json,re,hashlib,collections
E=Path(__file__).resolve().parent;R=E.parents[1]
g=json.loads((E/'NFY_SOURCE_GRAPH.json').read_text());paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=R,text=True).splitlines();paths=[p for p in paths if p.endswith('.lean') and not re.search(r'/[A-Z]+_L\d+/',p)]
for n in json.loads((E/'NFY_COPY_ORDER.json').read_text()):
 if n in g:continue
 ps=[p for p in paths if p.endswith('/'+n.replace('.','/')+'.lean') or p.endswith('/'+n+'.lean')]
 ps=sorted(ps,key=lambda p:(0 if p.startswith('lean/') else 1, bool(re.search('diagnostics|/sources/|/scratch/',p)),len(p),p))
 if not ps:print('MISSING',n);continue
 p=ps[0];t=(R/p).read_text() if (R/p).exists() else subprocess.check_output(['git','show','HEAD:'+p],cwd=R,text=True)
 g[n]=dict(path=p,source=t,sha256=hashlib.sha256(t.encode()).hexdigest(),imports=re.findall(r'^import ([\w.]+)',t,re.M))
(E/'NFY_SOURCE_GRAPH.json').write_text(json.dumps(g,indent=1)+'\n')
order=json.loads((E/'NFY_COPY_ORDER.json').read_text());print('modules',len(g),'remaining lines',sum(len(g.get(n,{}).get('source','').splitlines()) for n in order))
