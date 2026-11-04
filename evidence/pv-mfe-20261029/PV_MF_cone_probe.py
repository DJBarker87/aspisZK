from pathlib import Path
import json
D=Path(__file__).resolve().parent;j=json.load(open(D/'provenance-input.json'));g=next(v['content'] for k,v in j.items() if k.endswith('host-module-graph.json'));snapshot=next(v['content'] for k,v in j.items() if k.endswith('27828-input.json'));pins={v['module']:v['sha256'] for v in snapshot['dependencies']};probe=json.load(open(D/'provenance-probe.json'))[0];bad={v['module']:v for v in probe['mismatches']};gaps=json.load(open(D.parent/'pv-mfc-20261029/h7-review.json'))['modules'];out=[]
for x in gaps:
 m=x['module'];seen=set();missing=[]
 def walk(k):
  if k in seen:return
  seen.add(k)
  if k not in g:missing.append(k);return
  for d in g[k]['imports']:walk(d)
 if m in g:walk(m)
 out.append(dict(module=m,graph_entry=g.get(m),object_graph_reachable=len(seen),graph_missing=missing,missing_historical_hashes=sorted(seen-set(pins)),historical_current_mismatches=[bad[k] for k in sorted(seen&set(bad))],admissible=False,reason='No graph entry' if m not in g else 'Complete original transitive object hashes are missing and/or current hashes differ; no reuse or variant substitution'))
(D/'h7-cone-review.json').write_text(json.dumps(out,indent=2)+'\n')
for v in out:print(v['module'],v['object_graph_reachable'],'reachable',len(v['missing_historical_hashes']),'unpinned',len(v['historical_current_mismatches']),'mismatched')
