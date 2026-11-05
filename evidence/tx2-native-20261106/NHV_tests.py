"""Reject evidence mutations without submitting any prover/regression job."""
from pathlib import Path
import json,copy,subprocess,sys
import NHV_validate as v
E=Path(__file__).resolve().parent
a='NHV_K031';ad=json.loads((E/(a+'-admission.json')).read_text());r=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph-check.json')).read_text());l=json.loads((E/(a+'-lock-check.json')).read_text())
assert v.check(ad,r,g,l)
mutations=[('admission_exit',lambda a,r,g,l:a.update(exit=78)),('admission_false',lambda a,r,g,l:a['reservation'].update(allowed=False)),('dependency_graph',lambda a,r,g,l:g.update(graph_matches_frozen=False)),('lock_after',lambda a,r,g,l:l.update(after='0'*64)),('lock_unchanged',lambda a,r,g,l:l.update(unchanged=False)),('scope_limit',lambda a,r,g,l:r['limits'].update({'memory.max':'17179869184'})),('feature_drift',lambda a,r,g,l:next(z for z in g['all_crate_features'] if z['name']=='aspis-r1-cost-probe')['features'].append('prover')),('missing_feature_graph',lambda a,r,g,l:g.pop('all_crate_features'))]
results=[]
for name,mutate in mutations:
 aa,rr,gg,ll=map(copy.deepcopy,[ad,r,g,l]);mutate(aa,rr,gg,ll)
 try:v.check(aa,rr,gg,ll)
 except (AssertionError,KeyError):results.append(dict(test=name,rejected=True))
 else:raise AssertionError('Accepted mutation '+name)
(E/'NHV_TESTS.json').write_text(json.dumps(dict(status='PASS',mutations=results),indent=2)+'\n');print(json.dumps(dict(status='PASS',rejected=len(results))))
