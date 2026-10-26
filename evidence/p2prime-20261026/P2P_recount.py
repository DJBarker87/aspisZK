"""Reviewed Rc6 atomic-family mapping, checked against fresh P2P kernel inventories.
Output witnesses and derived source provenance are not antecedents. Shared guards,
witnesses, installed dictionaries and the existing charged event are deduplicated.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re,copy
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bp=R/'evidence/recount6-20261026/Rc6_premises.json';before=json.loads(bp.read_text())
plan=json.loads((P/'P2P_audit_plan.json').read_text());catalog={};evidence=[];logs={}
for a in plan:
 d=P/a['attempt'];r=json.loads((d/'receipt.json').read_text());assert r['exit_status']==0,a
 log=(d/'stdout.log').read_text();assert not re.search(r'\berror(?:\(|:)',log),a
 label=a['module'].removeprefix('P2P_Audit');logs[label]=log
 assert r['source_hashes'][a['module']+'.lean']==sha(R/'lean'/(a['module']+'.lean')),a
 evidence.append(dict(**a,source_sha256=sha(R/'lean'/(a['module']+'.lean')),stdout_sha256=sha(d/'stdout.log')))
 for block in re.split(r'(?=^structure )',log,flags=re.M):
  if not block.startswith('structure ') or 'fields:\n' not in block:continue
  key=re.match(r'structure (\S+)',block)[1]
  fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
  catalog[key]=dict(audit=label,fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
oldcat=json.loads((R/'evidence/recount6-20261026/Rc6_field_catalog.json').read_text());unchanged=[]
for k in oldcat.keys()&catalog.keys():
 assert catalog[k]['fields']==oldcat[k]['fields'],('changed retained structure',k)
 unchanged.append(k)
assert len(unchanged)>=15,len(unchanged)
# New full root and every new guard-bearing definition are inventoried.
for name in ['P2P_Top.deployed','P2P_Release.remove','P2P_Projection.good','P2P_Forget.forget']:
 assert name in logs['Composition'],name
newcaller=logs['Continuation'].split('def AspisR1.P2P_Caller.Outcome',1)[1].split('def AspisR1.Rc5_Cont.Outcome',1)[0]
assert 'P2Prime' not in newcaller
newresult=logs['Result'].split('def AspisR1.P2P_Result.Outcome',1)[1].split('def AspisR1.P2P_GoodResult.Outcome',1)[0]
assert 'P2Prime' not in newresult and 'bad ∨' in newresult
for name in ['P2P_Origin.Fact','PFin_Packet.Facts','P6C_OnCuts.SafeBatches','P6C_FullBoundary.Facts','P2P_Acceptance.Facts','P2P_Acceptance.Nonrejecting','P2P_Caller.Outcome']:
 assert name in newresult,name
old=(R/'lean/Rc6_Top.lean').read_text().split('theorem deployed',1)[1].split(' := by',1)[0]
new=(R/'lean/P2P_Top.lean').read_text().split('theorem deployed',1)[1].split(' := by',1)[0]
assert old.split('    (select :',1)[0].rstrip()==new.split('    : let select',1)[0].rstrip()
assert 'P2Prime' not in new
assert 'let select' in new and 'P2P_NativeSelection.pair' in new
assert new.count('F3T_AccountCharge.mass')==2 and new.count('Hiq_RecordedJoint.program')==1
removed={'L097','L098'};rows=[copy.deepcopy(r) for r in before['rows'] if r['id'] not in removed]
assert removed <= {r['id'] for r in before['rows']}
for r in rows:r.update(evidence='P2P fresh kernel inventories064-100; unchanged retained Rc6 atomic family')
def counts(rs):
 return dict(rows=len(rs),classes={c:sum(r['classification']==c for r in rs) for c in ['T','P','C']},by_owner={o:{c:sum(r['owner']==o and r['classification']==c for r in rs) for c in ['T','P','C']} for o in ['lead','session A','external']})
summary={s:counts([r for r in rows if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
summary['all retained audit rows']=counts(rows)
summary['deduplicated actual plus non-alias deployment']=counts([r for r in rows if r['scope']!='deployment alias'])
summary['actual excluding approved game domain']=counts([r for r in rows if r['scope']=='actual antecedent' and r.get('role')!='approved game domain'])
assert summary['actual antecedent']['classes']==dict(T=83,P=30,C=0)
assert summary['actual excluding approved game domain']['classes']==dict(T=83,P=19,C=0)
assert summary['deduplicated actual plus non-alias deployment']['classes']==dict(T=89,P=38,C=0)
assert summary['all retained audit rows']['classes']==dict(T=89,P=40,C=0)
result=dict(actual_theorem='AspisR1.P2P_Top.deployed',baseline=before['actual_theorem'],baseline_path=str(bp.relative_to(R)),baseline_sha256=sha(bp),method=__doc__,statement_evidence=evidence,unchanged_fresh_structure_inventories=sorted(unchanged),before_counts=before['counts'],counts=summary,removed_rows=sorted(removed),removed_actual_P=2,added_actual_T=0,added_actual_P=0,net_actual_P_delta=-2,net_deduplicated_P_delta=-2,rows=rows,analysis_projection_change='Arbitrary select replaced by deterministic native-entry selector, fixed before H; adversary/chooseSecond and their budgets unchanged. Actual new top event and numeric mass use that exact selector.',conclusion_change='P2Prime-guarded acceptance and continuation become SINGLE charged collision alternative OR their unguarded consequences; all other same-witness source facts remain unconditional.',caveat='No unconditional byte identity, joint accepted cryptographic fixture or release target established. Existing raw frozen3 join/runtime binding and all release gates retained.')
(P/'P2P_premises.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
(P/'P2P_field_catalog.json').write_text(json.dumps(catalog,indent=2,ensure_ascii=False)+'\n')
for label,module in [('BEFORE','Rc6_Top'),('AFTER','P2P_Top')]:
 s=(R/'lean'/(module+'.lean')).read_text();s=s[s.index('theorem deployed'):].split(' := by',1)[0]
 (P/f'P2P_{label}_STATEMENT.lean.txt').write_text(s+'\n')
(P/'P2P_EXPANDED_STATEMENTS.txt').write_text(logs['Composition']+'\n'+logs['Result']+'\n'+logs['Continuation']+'\n'+logs['Nonvacuity']+'\n'+logs['Selection'])
print(json.dumps(dict(counts=summary,removed=sorted(removed),unchanged_structures=len(unchanged)),indent=2))
