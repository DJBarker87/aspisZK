from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=E/'NNK_AUDIT_ROOTS.json';x=json.loads(p.read_text());(E/'NNK_PRE_COST_ROOTS.json').write_bytes(p.read_bytes());costs=json.loads((E/'NNK_COST_PREFLIGHT.json').read_text());assert len(costs)==566
bins=[[]for _ in range(9)];weights=[0.0]*9
for row in sorted(costs,key=lambda r:(-r['cost'],r['root'])):
 i=min(range(9),key=lambda i:(weights[i],len(bins[i]),i));bins[i].append(row['root']);weights[i]+=row['cost']
bins=[sorted(b)for b in bins];x['groups']=x['groups'][:42]+bins
assert len([r for g in x['groups']for r in g])==len(set(r for g in x['groups']for r in g))==12987
p.write_text(json.dumps(x,indent=1)+'\n');(E/'NNK_AUDIT_MODULES.json').write_text(json.dumps([['NNK_COMBINED_IMPORT']]*51,indent=1)+'\n')
plan=dict(status='REPLACEMENT_INPUT_SHAPES',timeouts=['NNK_L046','NNK_L048'],partial_credit=0,measured_uniform_last_window='55 partial roots over152.055 seconds; no single stalled root; all partial outputs retained',classification='Recorded reachability only for scheduling; no credit from reused candidate audit. LIB_VLib.library presence predicts repeated complete-library graph traversal. Unknown costs conservative.',windows=[dict(group=42+i,attempt=f'NNK_L{49+i:03}',roots=b,estimated_body_seconds=weights[i],full_library_roots=sum(next(c for c in costs if c['root']==r).get('library',True)for r in b))for i,b in enumerate(bins)],caps_unchanged=True,timeout_unchanged=True,no_unchanged_rerun=True,final_scopes={'58':'one new FinalStatements module: all three exact RowSpecs/domains plus complete12987 owner/type capture','59':'NFX scan','60':'pin/export, independent integrity and final retention, sequential'})
assert max(r['full_library_roots']for r in plan['windows'])<=30
(E/'NNK_COST_PLAN.json').write_text(json.dumps(plan,indent=1)+'\n');print([(r['group'],len(r['roots']),round(r['estimated_body_seconds'],1),r['full_library_roots'])for r in plan['windows']])
