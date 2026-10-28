"""Verify receipt integrity and exact local-claim inputs; no proof launch."""
from pathlib import Path
import json,hashlib,collections,subprocess,sys,re
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
rows=[json.loads(l) for l in (E/'NDD_ATTEMPTS.jsonl').read_text().splitlines()]
ids=[r['attempt'] for r in rows];assert len(ids)==len(set(ids))
byid={r['attempt']:r for r in rows};counts=collections.Counter(r['kind'] for r in rows)
assert sorted(r['attempt'] for r in rows if r['kind']=='kani')==[f'NDD_K{i:03}' for i in range(1,81)]
assert counts['lean']<=80 and counts['extract']<=20
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in rows:
 assert r['limits']==limits,(r['attempt'],r['limits'])
 assert int(r['swaps'])==0,r['attempt']
 assert r['source_revision'] and r['source_hashes']
 for n,h in r['source_hashes'].items():
  p=E/r['attempt']/'sources'/n
  assert p.is_file(),p
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h,(r['attempt'],n)
 if r['kind']!='kani':continue
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'] and not g['edge_errors'],a
 sc=json.loads((E/(a+'-source-check.json')).read_text());assert not sc['errors'],a
 lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
 cmd=r['native_command'];assert '--locked' not in cmd,a
 manifest=cmd[cmd.index('--manifest-path')+1];features=cmd[cmd.index('--features')+1]
 if 'aspis-r1-cost-probe' in manifest:assert features=='private-leaf-salts,optimized-terminal,program-build',a
 else:assert features=='r0',a
 assert g['all_crate_features']['aspis-core']==['r0'],a
 assert set(['default','private-leaf-salts','optimized-terminal','program-build'])<=set(g['all_crate_features']['aspis-r1-cost-probe']),a
 assert len([f for f in g['all_crate_features']['aspis-statement'] if f.startswith('pool-v1-pair-forest-')])==12,a
 assert r['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',a
patch=R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch'
assert hashlib.sha256(patch.read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
delta=json.loads((E/'NDD_LEDGER_DELTA.json').read_text());base=json.loads((R/'evidence/native-compledger-20261028/NCZ_LEDGER.json').read_text())
body_expected={r['function']:r['frozen_body_sha256'] for r in base['rows']}
markers={
'M31::reduce_u62':'pub fn reduce_u62(value: u64) -> M31 {',
'PreparedQm31Multiplier::new':'pub fn new(value: QM31) -> Self {',
'CM31::from_m31':'pub fn from_m31(a: M31) -> CM31 {',
'CM31::neg':'pub fn neg(self) -> CM31 {',
'M31::neg':'pub fn neg(self) -> M31 {',
'QM31::is_zero':'pub fn is_zero(self) -> bool {',
'qm31_from_karatsuba_channel_sums':'fn qm31_from_karatsuba_channel_sums(sums: [[u64; 3]; 3]) -> QM31 {'}
closed=[]
for c in delta['members']:
 if c['status']!='CLOSED-local':continue
 l=byid[c['lean_attempt']];k=byid[c['kani_attempt']];n=byid[c['negative_control']]
 assert l['exit_status']==0 and k['exit_status']==0
 assert all(not any(bad in s for bad in ['sorryAx','[axiom','source_reference,']) for s in l['print_axioms']),c['function']
 assert any(c['lean_theorem'] in s for s in l['print_axioms']),c['function']
 neg=(E/n['attempt']/'stdout.log').read_text();assert 'Failed Checks:' in neg and 'timed out' not in neg.lower()
 source=(E/k['attempt']/'sources/NDD_src/crates/aspis-core/src/field.rs').read_text()
 short=c['function'].split('field.rs::',1)[1]
 offset=source.index('impl QM31 {') if short=='QM31::is_zero' else 0
 start=source.index(markers[short],offset);a=source.index('{',start);depth=0
 for z in range(a,len(source)):
  if source[z]=='{':depth+=1
  elif source[z]=='}':
   depth-=1
   if depth==0:break
 digest=hashlib.sha256(source[a:z+1].encode()).hexdigest();assert digest==body_expected[c['function']],c['function']
 closed.append(dict(function=c['function'],body_sha256=digest,lean=c['lean_attempt'],native=k['attempt'],negative=n['attempt'],domain=c['domain']))
accepted=json.loads((E/'NDD_ACCEPTED_MODULES.json').read_text())
for m,v in accepted.items():
 p=E/(m+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==v['source_sha256']
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',p.read_text()),m
 if not m.startswith('NDD_Reference/'):
  assert 'maxHeartbeats' not in p.read_text() and 'maxRecDepth' not in p.read_text(),m
from NDD_sources import sources
sources()
result=dict(exit_status=0,budget=dict(counts),frozen_native_bodies=closed,unique_local_frontier_closures=len(closed),graphs_and_locks_checked=80,all_scopes=limits,standard_axiom_acceptance_only=True,harness_transport='new-file patch with exact input hashes',unconditional_composed_closures=0)
(E/'NDD_LOCAL_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='frozen_native_bodies'}))
