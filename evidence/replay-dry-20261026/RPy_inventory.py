"""Read-only committed-source availability inventory; never selects cached objects."""
from pathlib import Path
import subprocess,json,hashlib,collections
E=Path(__file__).resolve().parent; R=E.parents[1];g=json.loads((E/'RPy_graph.json').read_text()); files=subprocess.check_output(['git','ls-files','*.lean'],cwd=R,text=True).splitlines();bybase=collections.defaultdict(list)
for p in files:bybase[Path(p).name].append(p)
rows=[]
for m in g['order']:
 meta=g['modules'][m];suffix=m.replace('.','/')+'.lean';candidates=[p for p in bybase[Path(suffix).name] if p==suffix or p.endswith('/'+suffix)]
 preferred=[p for p in candidates if p in ['lean/'+suffix,'docs/research/100bit-spend-path-20261013/lean/'+suffix]]
 matches=[]
 if meta.get('source_sha256'):
  for p in candidates:
   if hashlib.sha256((R/p).read_bytes()).hexdigest()==meta['source_sha256']:matches.append(p)
 rows.append(dict(module=m,current_canonical_sources=preferred,historical_source_sha256=meta.get('source_sha256'),matching_committed_paths=matches,candidate_paths=candidates,status='toolchain source copied separately' if m.split('.')[0] in ['Init','Lean','Std','Lake'] else 'canonical available' if preferred else 'hash match available' if matches else 'unresolved source selection'))
(E/'RPy_source-availability.json').write_text(json.dumps(rows,indent=2)+'\n')
print(dict(collections.Counter(x['status'] for x in rows)))
