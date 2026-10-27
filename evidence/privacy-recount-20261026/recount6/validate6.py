from pathlib import Path
import json,hashlib,collections,subprocess,re
P=Path(__file__).resolve().parent;B=P.parent
load=lambda f:json.loads(f.read_text())
rows=load(P/'rows6.json');old=load(B/'recount5/rows5.json');t=load(P/'totals6.json');manifest=load(P/'manifest.json')
assert len(rows)==407 and [r['id'] for r in rows]==[r['id'] for r in old]
for r,o in zip(rows,old):
 for k,v in o.items():
  if k.startswith(('recount1','recount2','recount3','recount4','recount5','in_headline_closure','import_witnesses','definition_witnesses')):assert r[k]==v,(r['id'],k)
 assert r['recount5_bucket']==o['dependency_bucket']
 assert r['recount6_basis'] and r['recount6_evidence']
 assert r['dependency_bucket'] in 'abcd' if r['recount6_status']=='OPEN' else r['dependency_bucket'] is None
assert dict(collections.Counter(r['recount6_status'] for r in rows))==t['statuses']
assert sum(t['statuses'].values())==407 and sum(t['classes'].values())==407
assert sum(t['open_dependencies'].values())==86
assert t['statuses']['CLOSED-ON-CANDIDATE']==44 and t['classes']=={'P':400,'C':4,'T':3}
changed=[r['id'] for r in rows if r['recount5_status']!=r['recount6_status']]
assert set(changed)=={'V178','V184','V233','V247','V261','V264','V265'}
for x in manifest:
 raw=(P/x['snapshot']).read_bytes()
 assert hashlib.sha256(raw).hexdigest()==x['sha256'],x['path']
 assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['blob']
assert all(x['found'] for x in load(P/'evidence-audit6.json'))
assert all(x['matches'] for x in load(P/'closing-freeze-checks6.json'))
assert all(x['match'] for x in load(P/'native-pin-checks6.json'))
assert all(not x['unresolved'] for x in load(P/'closing-source-cones6.json'))
receipts=load(P/'reused-receipts6.json')
assert [x['id'] for x in receipts]==[37698,37699,37600,37604,38597,38598]
for x in receipts:assert x['receipt']['exit']==0 and x['standard_axioms']
assert [x['audit_queries'] for x in receipts]==[159,204,0,3,309,1]
ledger=Path('design/PRIVACY-LEDGER-20261026.md').read_bytes();base=subprocess.check_output(['git','show','0a32311d73ce1d37e5f3c35f7a03b8b9cbd78ffd:design/PRIVACY-LEDGER-20261026.md'])
assert ledger.startswith(base) and ledger.count(b'## Recount 6 2026-10-27 (B)')==1
assert sum(l.startswith('|V') for l in (B/'ROWS6.md').read_text().splitlines())==407
packet=Path('design/PV-OWNER-PACKET-20261027.md').read_text()
assert packet.count('**owner-APPROVED**')==2
for s in ['constant-time private-input','N7','SHA-NI','DOITM','Client scope','caller-supplied']:assert s in packet
pins=load(P/'pins.json');assert pins['revisions']['rw'].startswith('03905a5259')
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-recount6-20261027'
assert Path.cwd()==Path('/Users/dominic/ZK/.worktrees/pv-recount6')
report=dict(result='PASS',rows=407,status_changes=changed,manifest_records=len(manifest),definition_audit_rows=len(load(P/'definition-audit6.json')),closing_project_cones=len(load(P/'closing-source-cones6.json')),closing_freeze_occurrences=len(load(P/'closing-freeze-checks6.json')),required_reused_audits=[x['id'] for x in receipts],axiom_query_counts=[x['audit_queries'] for x in receipts],new_lean_invocations=0,lean_budget=20,new_kani_invocations=0,ids_used=[],reserved_ids='39200-39299',proofs_added=0,host_scopes=0,endpoint_removed_added_weakened=[0,0,0],ledger_historical_prefix_preserved=True,target='not yet established')
(P/'validation6.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
