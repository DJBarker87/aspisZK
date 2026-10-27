"""Fresh Rc6 kernel inventory with reviewed atomic-family correspondence.
Use the ledger's quantified-family, shared-guard/witness and dictionary-dedup
method. P/T/C classification is reviewed; output witnesses are not premises.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bp=R/'evidence/recount5-20261026/Rc5_premises.json';before=json.loads(bp.read_text())
plan=json.loads((P/'Rc6_audit_plan.json').read_text());logs={};catalog={};evidence=[]
for a in plan:
 d=P/a['attempt'];r=json.loads((d/'receipt.json').read_text());assert r['exit_status']==0,a
 log=(d/'stdout.log').read_text();assert not re.search(r'\berror(?:\(|:)',log),a
 name=a['module'].removeprefix('Rc6_Audit');logs[name]=log
 assert r['source_hashes'][a['module']+'.lean']==sha(R/'lean'/(a['module']+'.lean')),a
 evidence.append(dict(**a,source_sha256=sha(R/'lean'/(a['module']+'.lean')),stdout_sha256=sha(d/'stdout.log')))
 for block in re.split(r'(?=^structure )',log,flags=re.M):
  if not block.startswith('structure ') or 'fields:\n' not in block:continue
  key=re.match(r'structure (\S+)',block)[1]
  fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
  catalog[key]=dict(audit=name,fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
oldcat=json.loads((R/'evidence/recount5-20261026/Rc5_field_catalog.json').read_text())
unchanged=[]
for k in oldcat.keys()&catalog.keys():
 assert catalog[k]['fields']==oldcat[k]['fields'],('changed atomic structure',k)
 unchanged.append(k)
assert len(unchanged)>=15,len(unchanged)
root=logs['Composition'].split('@AspisR1.Rc6_Top.deployed :',1)[1].split('@AspisR1.Rc6_Statements.reverse :',1)[0]
for s in ['F3T_CanonicalJoin.AcceptedVerifierJoin','F3T_Runtime.StoredCarrierBinding','CPH_Game.DeployedPairExecution','CPR_DataPersistence.TwoTransactionLaw','Rc6_Result.Outcome','CPH_Protection.Facts','CPH_Trace.Facts','CPH_Recorder.Facts','MultiproofConeP6Frozen2Stage.P6Boundary']:
 assert s in root,s
for s in ['Port1_CanonicalJoin.AcceptedVerifierJoin','OraclePortRuntimeBindingC7.StoredCarrierBinding']:
 assert s not in root,s
caller=logs['Continuation'].split('def AspisR1.Rc6_Caller.Outcome',1)[1].split('@AspisR1.Rc6_Caller.from_cut',1)[0]
assert 'FirstEntryVerifierConeJoin' not in caller
assert 'S2W_AuthenticatedInputs.P2Prime' in caller and 'Rc5_Cont.Outcome' in caller
assert '∀ (ports :' not in logs['Literal']
for s in ['PFin_Packet.Facts','P6C_OnCuts.SafeBatches','P6C_FullBoundary.Facts','Rc6_Caller.Outcome','∃ version','version.events = events','Rc5_Nonvacuity.Facts']:
 assert s in logs['Result'],s
assert len(catalog['AspisR1.CPH_Game.DeployedPairExecution']['field_names'])==4
assert len(catalog['AspisR1.CPG_Projection.Observations']['field_names'])==9
assert len(catalog['AspisR1.SAF_ReducedLaws.Arithmetic']['field_names'])==3
# The concrete code constructs every new output on the existing witnesses.
strength=(R/'lean/Rc6_Result.lean').read_text();top=(R/'lean/Rc6_Top.lean').read_text()
for s in [':= source','P6C_OnCuts.same_cuts','P6C_FullBoundary.same_cuts','PFin_Packet.from_cut','Rc6_Caller.from_cut','pairCuts selected run','scanned.2.2']:
 assert s in strength,s
assert 'Rc5_Top.deployed' in top and 'Rc6_Result.strengthen' in top
assert 'PFin_Top.deployed' not in top and 'P6C_Top.deployed' not in top
assert 'intro p2 entry\n  exact caller p2' in (R/'lean/Rc6_Forget.lean').read_text()
# Before/after have identical explicit binders, including carrier, game and budgets.
bs=(P/'Rc6_before-statement.lean.txt').read_text();ass=(P/'Rc6_after-statement.lean.txt').read_text()
assert bs.split(' :\n    ',1)[0]==ass.split(' :\n    ',1)[0]
removed={'L099'}|{f'L{n}' for n in range(195,200)}
byid={r['id']:r for r in before['rows']};assert removed<=byid.keys()
assert byid['L099']['scope']=='actual antecedent'
assert all(byid[i]['scope']=='deployment only' for i in removed-{'L099'})
overlap={'L129','L130','L131','L132'}|{f'N{n}' for n in range(108,115)}
assert not overlap&byid.keys(),overlap&byid.keys()
def tag(r):
 i=r['id']
 if i=='L157':return 'F3X_'
 if i=='L159':return 'SCC_'
 if i=='L166':return 'BEf_'
 if r['owner']=='session A' and r['scope']=='actual antecedent':return 'SAG_'
 if i in {'L083','L084','L097','L098'} or r.get('role')=='approved game domain':return 'JFx_'
 return 'UNCOVERED'
rows=[];diff=[]
for old in before['rows']:
 r=dict(old)
 if r['id'] in removed:
  reason=('FirstEntry is constructed from PFin_Attach on Rc5 cuts; Rc6_Caller has no entry guard' if r['id']=='L099' else 'Accepted-run P6 refinement on the same Rc5 cuts and complete source logs; mathematical boundary derived on the defined extension')
  diff.append(dict(**r,change='removed',reason=reason,theorem='Rc6_Caller.from_cut' if r['id']=='L099' else 'Rc6_Result.strengthen / P6C_FullBoundary.same_cuts / P6C_Extension.boundary'));continue
 r.update(status='retained',running_job=tag(r),evidence='Rc6 fresh kernel inventories009–100; same-witness strengthen and full reverse transport001–008')
 if r['id']=='L187':r['blocker']='RELEASE GATE: coherent frozen dependency replay remains; focused pinned cache compilation is not that replay.'
 if r['id']=='L188':r['blocker']='RELEASE GATE: final release-wide trust/axiom audit remains; Rc6 theorem uses standard axioms only.'
 if r['id']=='L166':r['blocker']='BEf_ must bind the actual batch SDK child/native/global ordered effects; P6C_CarrierGap.independent shows the five mathematical P6 gates alone do not discharge this row.'
 if r['id']=='L159':r['blocker']='SCC_ covers the retained frozen3 stored runtime carrier association at the selected dictionary; no result from that job is imported here.'
 rows.append(r);diff.append(dict(**r,change='retained'))
def counts(rs):
 return dict(rows=len(rs),classes={c:sum(r['classification']==c for r in rs) for c in ['T','P','C']},by_owner={o:{c:sum(r['owner']==o and r['classification']==c for r in rs) for c in ['T','P','C']} for o in ['lead','session A','external']})
summary={s:counts([r for r in rows if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
summary['all retained audit rows']=counts(rows)
summary['deduplicated actual plus non-alias deployment']=counts([r for r in rows if r['scope']!='deployment alias'])
summary['actual excluding approved game domain']=counts([r for r in rows if r['scope']=='actual antecedent' and r.get('role')!='approved game domain'])
summary['deduplicated excluding approved game domain']=counts([r for r in rows if r['scope']!='deployment alias' and r.get('role')!='approved game domain'])
assert summary['actual antecedent']['classes']==dict(T=83,P=32,C=0)
assert summary['actual excluding approved game domain']['classes']==dict(T=83,P=21,C=0)
assert summary['deduplicated actual plus non-alias deployment']['classes']==dict(T=89,P=40,C=0)
assert summary['all retained audit rows']['classes']==dict(T=89,P=42,C=0)
result=dict(actual_theorem='AspisR1.Rc6_Top.deployed',baseline=before['actual_theorem'],baseline_path=str(bp.relative_to(R)),baseline_sha256=sha(bp),method=__doc__,statement_evidence=evidence,unchanged_fresh_structure_inventories=sorted(unchanged),counts=summary,before_counts=before['counts'],removed_actual_P=1,removed_deployment_P=5,removed_rows=sorted(removed),no_double_count_already_removed=sorted(overlap),added_actual_T=0,added_actual_P=0,net_actual_P_delta=-1,net_deduplicated_P_delta=-6,rows=rows,diff=diff,remaining_P_by_running_job=dict(Counter(r['running_job'] for r in rows if r['classification']=='P')),caveat='P6 delta is deployment-only. Seven SessionAPrepare leaves and four parser gates were already removed before Rc5. RuntimePersistence and eleven approved game clauses retained and counted. JFx_ remains a joint fixture obligation. L166 and release gates remain.')
(P/'Rc6_premises.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
(P/'Rc6_field_catalog.json').write_text(json.dumps(catalog,indent=2,ensure_ascii=False)+'\n')
lines=['# Remaining P rows on Rc6_Top','','Every tag is covering-job scope, not imported closure. JFx_ covers joint fixture instantiation, not universal discharge of accepted-event/P2Prime/game families. L187 and L188 are final release gates.','','| ID | Scope | Owner | Job | Family | Blocker |','|---|---|---|---|---|---|']
for r in rows:
 if r['classification']=='P':lines.append('| '+' | '.join(str(r.get(k,'')).replace('|','/').replace('\n',' ') for k in ['id','scope','owner','running_job','name','blocker'])+' |')
(P/'Rc6_REMAINING.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(counts=summary,removed=sorted(removed),coverage=result['remaining_P_by_running_job']),indent=2))
