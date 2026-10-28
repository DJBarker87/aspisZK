"""Check lane evidence and conservative delta; not an NCZ adoption override."""
from pathlib import Path
import json,hashlib,collections,importlib.util
E=Path(__file__).resolve().parent;R=E.parent.parent
load=lambda p:json.loads(p.read_text())
rows=[json.loads(l) for l in (E/'NDF_ATTEMPTS.jsonl').read_text().splitlines()]
by={r['attempt']:r for r in rows};assert len(by)==len(rows)
counts=collections.Counter(r['kind'] for r in rows)
assert counts['kani']<=50 and counts['lean']<=80 and counts['extract']<=20
for r in rows:
 assert all(k in r for k in ['module','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms'])
 assert str(r['swaps'])=='0'
 if r['kind']=='kani':
  a=r['attempt'];g=load(E/(a+'-graph-check.json'));lock=load(E/(a+'-lock-check.json'))
  assert g['graph_matches_frozen'] and lock['unchanged']
  features={p['name']:set(p['features']) for p in g['all_crate_features']}
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=features['aspis-r1-cost-probe']
  assert {'r0','pool-v1-kernel'}<=features['aspis-statement']
  assert len([x for x in features['aspis-statement'] if x.endswith('-audit')])>=12
  admission=load(E/(a+'-admission.json'));assert admission['exit']==0 and admission['reservation']['allowed'] is True
for a in [2,4,6,7,10,11,14,15,18,19,22,24,25,28,30,31,34,35,38,48]:
 assert by[f'NDF_K{a:03}']['exit_status']==0,a
for a in [3,5,8,9,12,13,16,17,20,21,23,26,27,29,32,33,36,37,39,49]:
 t=(E/f'NDF_K{a:03}'/'stdout.log').read_text()
 assert by[f'NDF_K{a:03}']['exit_status']!=0 and 'VERIFICATION:- FAILED' in t and 'timed out' not in t,a
assert 'timed out' in (E/'NDF_K050/stdout.log').read_text()
assert hashlib.sha256((R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
accepted=load(E/'NDF_ACCEPTED_MODULES.json')
for m,p in accepted.items():
 assert hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()==p['source_sha256']
 r=by[p['attempt']];assert r['exit_status']==0
 assert 'sorryAx' not in str(r['print_axioms'])
assert by['NDF_L032']['exit_status']==0
assert len(by['NDF_L032']['print_axioms'])==29
for line in by['NDF_L032']['print_axioms']:assert 'sorryAx' not in line
front=load(E/'NDF_FRONTIER.json');d=load(E/'NDF_LEDGER_DELTA.json')
assert {r['function'] for r in d['functions']}=={r['representative'] for r in front}
assert len(d['functions'])==24 and d['new_local_conditional_bridges']==6
assert all(r['composed_status']=='OPEN' for r in d['functions'])
base=load(E/'NDF_LEDGER_BASE.json');copy=dict(base,pending_local_bridge_delta=d)
(E/'NDF_LEDGER_UPDATED.json').write_text(json.dumps(copy,indent=2,sort_keys=True)+'\n')
spec=importlib.util.spec_from_file_location('NCZ',R/'evidence/native-compledger-20261028/NCZ_validate.py');nc=importlib.util.module_from_spec(spec);spec.loader.exec_module(nc);nc.validate_invariants(copy)
assert copy['rows']==base['rows'] and copy['claims']==base['claims']
result=dict(exit_status=0,attempt_counts=dict(counts),accepted_modules=len(accepted),new_top_theorems=29,local_conditional_bridges=6,composed_closures=0,canonical_ncz_invariants='PASS, unchanged canonical statuses',ncz_recompute='Requires explicit report-corpus/evidence snapshot refresh; retained failing run is not overridden.',remaining_open=18)
(E/'NDF_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
