from pathlib import Path
import json,hashlib
B=Path.cwd();load=lambda n:json.loads((B/n).read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();standard={'propext','Classical.choice','Quot.sound'}
roots=[]
for p in sorted((B/'NJG_audit').glob('batch*/*.json')):
 r=load(str(p.relative_to(B)));assert r['exit_status']==0
 for q in r['results']:
  assert q['equal'] and set(q['walked_axioms'])<=standard and set(q['collect_axioms'])<=standard,q['root']
  roots.append(q['root'])
assert len(roots)==len(set(roots))==100
scan=[json.loads(l) for l in (B/'NJG_LOADED_scan.jsonl').read_text().splitlines()]
assert all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in scan)
pairs=[('K003','K002'),('K004','K005'),('K006','K007'),('K008','K009'),('K016','K017'),('K018','K019'),('K024','K025'),('K026','K027')]
for pos,neg in pairs:
 for n,status in [(pos,0),(neg,1)]:
  a='NJG_'+n;r=load(a+'/receipt.json');assert r['exit_status']==status,(a,status)
  assert load(a+'-graph-check.json')['graph_matches_frozen']
  assert load(a+'-lock-check.json')['unchanged']
  assert not load(a+'-source-check.json')['errors']
  assert r['env']['CARGO_NET_OFFLINE']=='true'
assert load('NJG_EXTRACTION_RESTORED.json')['restored']
assert load('NJG_EXPORT_CHECK.json')['status']=='PASS'
x=load('NJG_ASSERTIONS.json');assert sha(B/'NJG_FINAL_NATIVE.patch')==x['patch_sha256']
assert x['kmx_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
consumer=load('NJG_L097/receipt.json');assert consumer['exit_status']==0 and '/NJG_objects' not in consumer['env']['LEAN_PATH']
out=dict(status='PASS_LOCAL_SUPPORT_ONLY',raw_roots=len(roots),loaded_modules=len(scan),valid_native_pairs=pairs,complete_consumer_import=True,new_closed_rows=0,security_target_established=False,known_exclusions=['F2 current-row initialization pairs','F5 local rather than absolute error-index pairs','Failed Lean drafts','Source/model op9 interpreted as native base op9'])
(B/'NJG_VALIDATION.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
