"""Validate retained native pairs without replaying a native job."""
from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
rows=json.loads((E/'NKO_NATIVE_PAIRS.json').read_text())['pairs']
for p,c,label in [(38,39,'t slice ensures'),(44,45,'t borrowed query ensures'),(50,51,'t latest borrowed query ensures'),(52,53,'C07 verified-contract byte frame'),(54,55,'C07 real-body byte frame'),(56,57,'C07 owned-call byte frame'),(58,59,'C07 owned Result descriptors')]:
 a,b=f'NKO_K{p:03}',f'NKO_K{c:03}'
 if not (E/b/'receipt.json').exists():continue
 if not any(r['positive']==a for r in rows):rows.append(dict(positive=a,control=b,kind=label,raw_no_return=False))
for r in rows:
 a,b=[json.loads((E/r[k]/'receipt.json').read_text()) for k in ['positive','control']]
 assert a['source_hashes']==b['source_hashes'],r
 assert a['exit_status']==(1 if r.get('raw_no_return') else 0),r
 assert b['exit_status']==1,r
 for n in [r['positive'],r['control']]:
  g=json.loads((E/(n+'-graph-check.json')).read_text());l=json.loads((E/(n+'-lock-check.json')).read_text());s=json.loads((E/(n+'-source-check.json')).read_text())
  assert g['graph_matches_frozen'] and not g['edge_errors'] and not g['new_package_tuples'] and l['unchanged'] and not s['errors'],n
  log=(E/n/'stdout.log').read_text();assert 'VERIFICATION:-' in log and 'TIMEOUT' not in log,n
 if not r.get('raw_no_return'):
  assert 'VERIFICATION:- SUCCESSFUL' in (E/r['positive']/'stdout.log').read_text(),r
  assert 'VERIFICATION:- FAILED' in (E/r['control']/'stdout.log').read_text(),r
 r.update(positive_exit=a['exit_status'],control_exit=b['exit_status'],same_source_hashes=True,graph_lock_source_checks=True)
(E/'NKO_NATIVE_PAIRS.json').write_text(json.dumps(dict(pairs=rows),indent=2)+'\n')
controls=[]
for a,check in [(40,'real tag'),(41,'unimplied stub tag'),(42,'assigns violation'),(46,'full real tag'),(47,'full unimplied stub tag'),(48,'full assigns violation'),(49,'restored out-of-frame assigns violation')]:
 n=f'NKO_K{a:03}';r=json.loads((E/n/'receipt.json').read_text());log=(E/n/'stdout.log').read_text();assert r['exit_status']==(0 if a in [40,46] else 1)
 assert 'VERIFICATION:- '+('SUCCESSFUL' if a in [40,46] else 'FAILED') in log
 failed=re.findall(r'^(Check [^\n]+)\n\s*- Status: FAILURE',log,re.M)
 if a in [42,48,49]:assert any('assigns' in x for x in failed),(n,failed)
 controls.append(dict(attempt=n,check=check,exit_status=r['exit_status'],failed_properties=failed))
(E/'NKO_CONTRACT_CONTROLS.json').write_text(json.dumps(dict(controls=controls,transport='P6/D188 option A reclassification; not removal',owned_contract_K043='TIMEOUT retired; not admitted'),indent=2)+'\n')
print(json.dumps(dict(validated_pairs=len(rows),fidelity_controls=len(controls))))
