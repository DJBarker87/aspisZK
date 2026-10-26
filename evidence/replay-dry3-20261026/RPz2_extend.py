from pathlib import Path
import json
E=Path(__file__).resolve().parent;g=json.loads((E/'RPz2_source-plan.json').read_text());r=json.loads((E/'RPz2_host-recovery.json').read_text());new=[]
for m,x in r['recovered'].items():
 if m=='R1NaturalProjection':continue
 text=x.pop('text');x.update(source=x['host_source'],snapshot=str((E/'RPz2_recovered'/Path(m.replace('.','/')+'.lean')).relative_to(E.parents[1])),recovery_pin={'revision':'retained-host-source-snapshot','sha256':x['sha256'],'path':x['host_source']})
 p=E.parents[1]/x['snapshot'];p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text);g['modules'][m]=x;new.append(m)
order=[];seen=set();active=set();trusted={'Init','Lean','Std','Lake','Mathlib','Aeneas','AeneasMeta','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Cli'}
def visit(m):
 if m in active:raise Exception('cycle '+m)
 if m in seen:return
 seen.add(m);x=g['modules'].get(m)
 if x is None:x={'kind':'trusted-library' if m.split('.')[0] in trusted else 'unresolved'};g['modules'][m]=x
 if x['kind']!='repository':return
 active.add(m)
 for n in x['imports']:visit(n)
 active.remove(m);order.append(m)
visit('Rc7_Top');g['order']=order;g['unresolved']=sorted(m for m in seen if g['modules'][m]['kind']=='unresolved');g['host_recovered']=new
D={}
def distance(m,d):
 if D.get(m,-1)>=d:return
 D[m]=d
 for n in g['modules'][m].get('imports',[]):distance(n,d+1)
distance('Rc7_Top',0);g['distance_to_top']=D
(E/'RPz2_source-plan.json').write_text(json.dumps(g,indent=2)+'\n');print('selected',len(order),'unresolved',len(g['unresolved']),'host recovery',len(new))
