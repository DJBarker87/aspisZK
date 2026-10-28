from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');p=D.parent/'codex-pv-rdb1-20261028/unit-graph.json';raw=p.read_bytes();j=json.loads(raw);U=j['units'];reach=set(j['roots']);q=list(reach);excluded=[]
while q:
 i=q.pop()
 for dep in U[i]['dependencies']:
  n=dep['index'];u=U[n];kind=u['target']['kind']
  if 'custom-build' in kind or 'proc-macro' in kind:excluded.append(dict(from_index=i,index=n,target=u['target'],reason='build script or compile-time proc macro boundary'));continue
  if n not in reach:reach.add(n);q.append(n)
rows=[]
for x in json.loads((D/'site-reconciliation.json').read_text())['MIR_candidates']:
 crate=Path(x['mir']).name.rsplit('-',1)[0]
 candidates=[i for i,u in enumerate(U) if u['target']['name'].replace('-','_')==crate]
 rows.append(dict(candidate_id=x['id'],crate=crate,unit_indices=candidates,runtime_indices=[i for i in candidates if i in reach],compile_time_only=bool(candidates) and not any(i in reach for i in candidates)))
(D/'runtime-unit-closure.json').write_text(json.dumps(dict(unit_graph_sha256=hashlib.sha256(raw).hexdigest(),roots=j['roots'],root_targets=[U[i]['target'] for i in j['roots']],runtime_indices=sorted(reach),excluded_boundaries=excluded,candidates=rows),indent=2)+'\n')
for x in rows:print(x)
