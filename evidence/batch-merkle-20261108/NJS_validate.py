"""Strict local evidence consistency gate; never awards authoritative ledger credit."""
from pathlib import Path
import collections,hashlib,json,lzma,re
from NJS_resolve import read
E=Path(__file__).resolve().parent
J=lambda n:json.loads(read(n))
S=lambda n:read(n).decode()
closed=J('NJS_CLOSED.json');packets=J('NJS_ROW_PACKETS.json');baseline={r['row']:r for r in J('NJS_BASELINE_ROWS.json')}
rows=[r for f in closed['functions'] for r in f['rows']]
assert len(rows)==len(set(rows))==len(packets)==19
assert set(rows)=={r['row'] for r in packets}
std={'propext','Classical.choice','Quot.sound'}
raw=J('NJS_audit/batch0/proof0.json');assert raw['exit_status']==0 and len(raw['results'])==40
assert {x['root'] for x in raw['results']}==set(J('NJS_AUDIT_ROOTS.json')['groups'][0])
for r in raw['results']:assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms']) and set(r['walked_axioms'])<=std
fixture=J('NJS_audit/fixtures/fixtures.json');assert fixture['exit_status']==0 and len(fixture['results'])==8
for r in fixture['results']:assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])
assert all(r['walked_axioms'] for r in fixture['results'][:4]) and all(not r['walked_axioms'] for r in fixture['results'][4:])
scan=list(map(json.loads,S('NJS_LOADED_scan.jsonl').splitlines()));assert len(scan)==15713
for r in scan:assert r['imports_match'] and not r['dangling'] and not r['duplicate_owners']
assert J('NJS_audit/scan2/scan.json')['exit_status']==0
pairs=sorted(set(tuple(pair) for f in closed['functions'] for pair in f['native_pairs']))
for good,bad in pairs:
 for a,verdict,status in [(good,'SUCCESSFUL',0),(bad,'FAILED',1)]:
  receipt=J(a+'/receipt.json');assert receipt['exit_status']==status
  log=S(a+'/stdout.log');assert 'VERIFICATION:- '+verdict in log
  if status:
   direct='Failed Checks: assertion failed' in log
   formatted=("Failed Checks: This is a placeholder message; Kani doesn't support message formatted at runtime" in log and 'in core::panicking::assert_failed_inner' in log)
   assert direct or formatted, (a,'not a semantic assertion failure')
  graph=J(a+'_validation/NHR_GRAPH_CHECK.json');lock=J(a+'_validation/NJS_LOCK.json');inputs=J(a+'_validation/NJS_INPUTS.json')
  assert graph['graph_matches_frozen'] and lock['unchanged'] and lock['before']==lock['after']
  assert inputs['frozen_revision']==closed['frozen_revision'] and inputs['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert receipt['env']['CARGO_NET_OFFLINE']=='true' and receipt['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert '--locked' not in inputs['native_command']
  assert inputs['cargo_target'].endswith('/codex-cx-batch-merkle-20261108/NJS_target')
  for n,h in receipt['source_hashes'].items():assert hashlib.sha256(read(a+'/sources/'+n)).hexdigest()==h,(a,n)
 g,b=J(good+'/receipt.json'),J(bad+'/receipt.json');assert g['source_hashes']==b['source_hashes'],(good,bad,'different inputs')
 assert '--cfg NJS_invert' not in g['env']['RUSTFLAGS'] and '--cfg NJS_invert' in b['env']['RUSTFLAGS']
for p in packets:
 o=baseline[p['row']];assert p['frozen_body_sha256']==o['frozen_body_sha256'] and p['obligation_statement_hash']==o['obligation_statement_hash']
 assert {x['id'] for x in p['caller_clauses']}=={x['id'] for x in o['obligation']['caller_domain_obligations']}
 assert all(c.get('discharged_by') for c in p['caller_clauses'])
 assert set(p['lean_roots'])<=set(J('NJS_AUDIT_ROOTS.json')['groups'][0])
for name,ref in J('NJS_POOLED_INPUTS.json').items():assert hashlib.sha256(read(name)).hexdigest()==ref['sha256']
assert J('NJS_final_preflight/NHR_GRAPH_CHECK.json')['graph_matches_frozen']
a=[json.loads(l) for l in S('NJS_ATTEMPTS.jsonl').splitlines()]
assert sum(x['kind']=='extract' for x in a)==1
for r in a:
 assert str(r['swaps'])=='0' and r['exit_status'] not in [124,137,-9]
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 admit=J(r['attempt']+'-admission.json');assert admit['exit']==0 and admit['reservation']['allowed'] is True
assert not [q for q in E.rglob('*') if q.is_file() and q.stat().st_size>20_000_000]
result={'status':'PASS','candidate_rows':19,'remaining_rows':7,'native_pairs':len(pairs),'raw_roots':40,'fixture_roots':8,'scan_modules':len(scan),'standard_axioms':sorted(std),'budgets_used':dict(collections.Counter(x['kind'] for x in a)),'authoritative_credit':False,'security_target_established':False}
(E/'NJS_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
