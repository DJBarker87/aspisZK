"""Read-only provenance check of the inherited selected source cohort."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];O=R/'evidence/replay-dry8-20261026'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=read(R/'evidence/replay-dry6-20261026/RPz5_source-plan.json');union=read(R/'evidence/replay-dry6-20261026/RPz5_tx1-probe-source-plan.json');p7=read(O/'RPz7_plan.json');checks=[];errors=[]
for m in base['order']:
 x=base['modules'][m];p=R/x['source'];actual=sha(p);row={'kind':'planning-input','module':m,'path':x['source'],'matches':actual==x['sha256']};checks.append(row)
 if not row['matches']:errors.append({**row,'expected':x['sha256'],'actual':actual})
for m,view in p7['reuse'].items():
 x=(union if view=='RPz5_union_overlay' else base)['modules'][m];p=R/x['source'];actual=sha(p);row={'kind':'actually-selected-reused-source','module':m,'path':x['source'],'matches':actual==x['sha256']};checks.append(row)
 if not row['matches']:errors.append({**row,'expected':x['sha256'],'actual':actual})
for f in O.glob('RPz7_*/receipt.json'):
 d=read(f)
 if d['exit_status']!=0 or d['module'].startswith('RPz7_Audit'):continue
 for path,expected in d['source_hashes'].items():
  p=O/Path(path).name;actual=sha(p);row={'kind':'inherited-compiler-snapshot','module':d['module'],'path':str(p.relative_to(R)),'matches':actual==expected};checks.append(row)
  if not row['matches']:errors.append({**row,'expected':expected,'actual':actual})
out={'planning_inputs':len(base['order']),'selected_reused_sources':len(p7['reuse']),'inherited_compiler_snapshots':sum(r['kind']=='inherited-compiler-snapshot' for r in checks),'errors':errors,'checks':checks};(E/'RPz8_selected-source-check.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='checks'});assert not errors,errors
