from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent;L=R/'lean'
graph=json.loads((P/'FIq_semantic-preflight.json').read_text()); missing={m:v for m,v in graph.items() if v['object'] is None}
for m,v in missing.items():
 if v['source'] is None:
  xs=list((R/'docs').rglob(m+'.lean'))
  if xs:v['source']=str(xs[0].relative_to(R))
  else:raise RuntimeError(m)
rename={m:'FIq_S_'+m.split('.')[-1] for m in missing}
rename.update({m:v['reuse_module'] for m,v in graph.items() if 'reuse_module' in v})
order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m);s=(R/missing[m]['source']).read_text()
 for line in s.splitlines():
  if line.startswith('import '):
   for n in line[7:].split():
    if n in missing:visit(n)
 order.append(m)
for m in missing:visit(m)
for m in order:
 s=(R/missing[m]['source']).read_text()
 s=re.sub(r'^set_option max(?:Heartbeats|RecDepth).*\n','',s,flags=re.M)
 s=re.sub(r'^import (.+)$',lambda mt:'import '+' '.join(rename.get(n,n) for n in mt[1].split()),s,flags=re.M)
 (L/(rename[m]+'.lean')).write_text(s)
(P/'FIq_semantic-order.json').write_text(json.dumps([{'module':rename[m],'original':m,**missing[m]} for m in order],indent=2)+'\n')
print('missing',len(order))
