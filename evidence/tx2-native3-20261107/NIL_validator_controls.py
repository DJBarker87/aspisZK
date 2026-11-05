"""Exercise fail-closed checks on copied receipt values; never change receipts."""
from pathlib import Path
import importlib.util,json,copy,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('NIL_validation',E/'NIL_BaseValidation.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
read=lambda n:json.loads((E/n).read_text())
a='NIL_K082';base=[read(a+'-admission.json'),read(a+'/receipt.json'),read(a+'-graph-check.json'),read(a+'-lock-check.json')]
assert m.check(*base)
cases={
 'reservation_denied':lambda v:v[0]['reservation'].update(allowed=False),
 'exit78_not_launch':lambda v:v[0].update(exit=78),
 'graph_drift':lambda v:v[2].update(graph_matches_frozen=False),
 'lock_drift':lambda v:v[3].update(after='drift'),
 'lock_unchanged_false':lambda v:v[3].update(unchanged=False),
 'swap_enabled':lambda v:v[1]['limits'].update({'memory.swap.max':'1'}),
 'memory_cap_raised':lambda v:v[1]['limits'].update({'memory.max':'17179869184'}),
 'missing_feature_graph':lambda v:v[2].pop('all_crate_features'),
 'deployed_feature_missing':lambda v:next(r for r in v[2]['all_crate_features'] if r['name']=='aspis-r1-cost-probe')['features'].remove('private-leaf-salts'),
}
results=[]
for name,mutate in cases.items():
 v=copy.deepcopy(base);mutate(v)
 try:m.check(*v)
 except AssertionError as e:results.append(dict(name=name,rejected=True,reason=str(e)))
 else:raise AssertionError('validator accepted '+name)
out=dict(status='PASS',positive=True,negative_controls=results,receipts_modified=False)
(E/'NIL_VALIDATOR_CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status='PASS',negative_controls=len(results))))
