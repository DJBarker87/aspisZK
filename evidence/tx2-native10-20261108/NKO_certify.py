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
 for rec in [a,b]:
  assert rec['env']['CARGO_NET_OFFLINE']=='true' and rec['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert rec['env']['CARGO_TARGET_DIR'].endswith('/codex-cx-tx2-native10-20261108/NKO_target')
  assert rec['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert '--locked' not in rec['native_command'] and 'private-leaf-salts,optimized-terminal,program-build' in rec['native_command']
 for n in [r['positive'],r['control']]:
  g=json.loads((E/(n+'-graph-check.json')).read_text());l=json.loads((E/(n+'-lock-check.json')).read_text());s=json.loads((E/(n+'-source-check.json')).read_text())
  assert g['graph_matches_frozen'] and not g['edge_errors'] and not g['new_package_tuples'] and l['unchanged'] and not s['errors'],n
  log=(E/n/'stdout.log').read_text();assert 'VERIFICATION:-' in log and 'TIMEOUT' not in log,n
 if r.get('raw_no_return'):
  positive=(E/r['positive']/'stdout.log').read_text();control=(E/r['control']/'stdout.log').read_text()
  marker='inactive_short_no_return' if r['positive']=='NKO_K007' else 'finish_short_no_return'
  pattern=r'Check [^\n]*'+marker+r'\.assertion\.1\n\s*- Status: '
  assert re.search(pattern+'SUCCESS',positive) and re.search(pattern+'FAILURE',control),r
  failures=re.findall(r'^(Check [^\n]+)\n\s*- Status: FAILURE',positive,re.M)
  assert failures and all('slice_index_fail::do_panic::runtime.assertion' in x for x in failures),r
  r['continuation_positive']='SUCCESS';r['continuation_control']='FAILURE';r['expected_abort_properties']=failures
 if not r.get('raw_no_return'):
  assert 'VERIFICATION:- SUCCESSFUL' in (E/r['positive']/'stdout.log').read_text(),r
  assert 'VERIFICATION:- FAILED' in (E/r['control']/'stdout.log').read_text(),r
 r.update(positive_exit=a['exit_status'],control_exit=b['exit_status'],same_source_hashes=True,graph_lock_source_checks=True)
(E/'NKO_NATIVE_PAIRS.json').write_text(json.dumps(dict(pairs=rows),indent=2)+'\n')
controls=[]
for a,check in [(40,'real tag'),(41,'unimplied stub tag'),(42,'assigns violation'),(46,'full real tag'),(47,'full unimplied stub tag'),(48,'full assigns violation'),(49,'restored out-of-frame assigns violation'),(60,'final-source restored write diagnostic; no extra admission')]:
 n=f'NKO_K{a:03}';r=json.loads((E/n/'receipt.json').read_text());log=(E/n/'stdout.log').read_text();assert r['exit_status']==(0 if a in [40,46] else 1)
 assert 'VERIFICATION:- '+('SUCCESSFUL' if a in [40,46] else 'FAILED') in log
 failed=re.findall(r'^(Check [^\n]+)\n\s*- Status: FAILURE',log,re.M)
 if a in [42,48,49,60]:assert any('assigns' in x for x in failed),(n,failed)
 controls.append(dict(attempt=n,check=check,exit_status=r['exit_status'],failed_properties=failed))
(E/'NKO_CONTRACT_CONTROLS.json').write_text(json.dumps(dict(controls=controls,transport='P6/D188 option A reclassification; not removal',owned_contract_K043='TIMEOUT retired; not admitted'),indent=2)+'\n')
print(json.dumps(dict(validated_pairs=len(rows),fidelity_controls=len(controls))))
