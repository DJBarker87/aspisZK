"""Audit the resolved graph against the unchanged release lock; never repair it."""
import json,tomllib,hashlib
from pathlib import Path
E=Path(__file__).resolve().parent
lock=tomllib.loads(Path('Cargo.lock').read_text())
m=json.loads((E/'LPd_GRAPH001/stdout.log').read_text())
key=lambda p:(p['name'],p['version'],p.get('source'))
frozen={key(p):p for p in lock['package']}
actual={key(p):p for p in m['packages']}
new=sorted(set(actual)-set(frozen),key=str)
nodes={x['id']:x for x in m['resolve']['nodes']}; pkgs={p['id']:p for p in m['packages']}
root=next(p['id'] for p in m['packages'] if p['name']=='aspis-r1-cost-probe')
seen=set()
def visit(i):
 if i in seen:return
 seen.add(i)
 for d in nodes[i]['dependencies']:visit(d)
visit(root)
reach=[dict(name=pkgs[i]['name'],version=pkgs[i]['version'],source=pkgs[i]['source'],features=nodes[i]['features']) for i in sorted(seen)]
edge_errors=[]
for parent in m['packages']:
 allowed=frozen[key(parent)].get('dependencies',[])
 for depid in nodes[parent['id']]['dependencies']:
  dep=pkgs[depid]; variants=[p for p in frozen if p[0]==dep['name']]
  # Cargo lock names omit version when unambiguous; otherwise use exact version/source.
  matches=[]
  for label in allowed:
   fields=label.split(' ')
   if fields[0]!=dep['name']:continue
   if len(fields)>1 and fields[1]!=dep['version']:continue
   if len(fields)==1 and len(variants)>1:continue
   if len(fields)>2 and fields[2].strip('()')!=dep.get('source'):continue
   matches.append(label)
  if not matches:edge_errors.append([key(parent),key(dep)])
out={'edge_errors':edge_errors,'lock_sha256' :hashlib.sha256(Path('Cargo.lock').read_bytes()).hexdigest(),'new_package_tuples':new,'resolved_packages':len(actual),'frozen_packages':len(frozen),'selected_cost_probe_closure':reach,'drifted_crates_reached':[p for p in reach if p['name'] in ['cfg-if','libc']],'graph_matches_frozen_package_selection':not new,'graph':[dict(id=i,dependencies=nodes[i]['dependencies'],features=nodes[i]['features']) for i in sorted(nodes)]}
(E/'LPd_GRAPH-CHECK.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['graph','selected_cost_probe_closure']},indent=2))
assert not new and not edge_errors,(new,edge_errors)
