from pathlib import Path
import json,hashlib,copy,lzma
E=Path('/Users/dominic/ZK/.worktrees/cx-ledger14/evidence/verify-observed5-20261107')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def verify(c):
 assert c['security_target_established']is False and c['root137_closed']is False and c['finish136_closed']is False and c['prepare_op9_instantiated']is False,'parent overclaim'
 assert c['headline']=='AspisR1.RPx_Deployed.deployed'
 assert sorted(r for x in c['functions'] for r in x['rows'])==['TX1:142','TX1:156','TX1:215']
 declared={x for g in json.loads((E/'NIX_AUDIT_ROOTS.json').read_text())['groups'] for x in g};measured={}
 for p in sorted((E/'NIX_audit').glob('batch*/proof*.json')):
  r=json.loads(p.read_text());assert r['exit_status']==0
  for t in r['results']:
   assert t['equal'] and t['collect_axioms']==t['walked_axioms'] and set(t['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound'])
   measured[t['root']]=t
 assert declared==set(measured),'raw root coverage'
 assert json.loads((E/'NIX_L093/receipt.json').read_text())['exit_status']==0
 scan=[json.loads(l) for l in (E/'NIX_LOADED_scan.jsonl').read_text().splitlines()]
 assert all(r['imports_match'] and not r['dangling'] and not r.get('duplicate_owners',[]) for r in scan)
 assert json.loads((E/'NIX_L099/receipt.json').read_text())['exit_status']==0
 fixture=json.loads((E/'NIX_audit/fixtures/fixtures.json').read_text());old=json.loads((E.parent/'verify-observed4-20261107/NIH_audit/fixtures/fixtures.json').read_text());assert fixture['exit_status']==0 and len(fixture['results'])==8
 for a,b in zip(fixture['results'],old['results']):assert a==b,'unchanged raw audit calibration'
 for x in c['functions']:
  assert x['root_domain'] and x['complete_carrier']is True and x['callee_packets'] and x['premise_policy'] and x['trust']
  assert set(x['lean_roots'])<=set(measured)
  for pos,neg in x['native_pairs']:
   p=json.loads((E/pos/'receipt.json').read_text());n=json.loads((E/neg/'receipt.json').read_text());pl=(E/pos/'stdout.log').read_text();nl=(E/neg/'stdout.log').read_text()
   assert p['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL'in pl
   assert n['exit_status']!=0 and 'VERIFICATION:- FAILED'in nl and 'CBMC timed out'not in nl and 'unwinding failures'not in nl
 # Every real native command has its OWN strict graph and post-lock receipt.
 graphs=list(E.glob('NIX_K*-graph-check.json'));locks=list(E.glob('NIX_K*-lock-check.json'))
 assert len(graphs)==100 and len(locks)==100,(len(graphs),len(locks))
 for p in graphs:assert json.loads(p.read_text())['graph_matches_frozen']is True
 for p in locks:
  r=json.loads(p.read_text());assert r['unchanged']is True and r['before']==r['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 for p in E.glob('NIX_MODULES.json'):
  for r in json.loads(p.read_text()):assert sha(E/(r['module']+'.lean'))==r['sha256'],'current-source receipt mismatch'
 assert sha(E/'NIX_KMX.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 return dict(status='PASS',candidate_rows=3,raw_roots=len(measured),modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),cached_replicas=sum(len(r.get('cached_replicas',[])) for r in scan),native_verification_invocations=len(graphs),fixture_controls=8,root137_closed=False,finish136_closed=False,op9_closed=False)
c=json.loads((E/'NIX_CLOSED.json').read_text());out=verify(c);denials=[]
for flag in ['root137_closed','finish136_closed','prepare_op9_instantiated','security_target_established']:
 d=copy.deepcopy(c);d[flag]=True
 try:verify(d)
 except AssertionError:denials.append(flag)
 else:raise AssertionError('overclaim denial did not fire')
for flag in ['root_domain','complete_carrier','callee_packets','lean_roots']:
 d=copy.deepcopy(c);d['functions'][0][flag]=False if flag=='complete_carrier'else [] if flag in ['callee_packets','lean_roots']else ''
 if flag=='lean_roots':d['functions'][0][flag]=['NIX_missing_root']
 try:verify(d)
 except AssertionError:denials.append(flag)
 else:raise AssertionError('packet denial did not fire')
out['denial_controls']=denials
(Path('/Users/dominic/ZK/.worktrees/cx-ledger14/evidence/ledger14-20261108/NJK_NIX_REVALIDATION.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
