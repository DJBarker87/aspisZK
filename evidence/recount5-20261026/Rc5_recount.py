"""Ledger_003–005: reviewed atomic-family correspondence; mechanical enumeration.
Preserve quantified families, shared guards and existential witnesses. Split
structure/conjunction inputs; distinguish output witnesses and approved game
conditions. Classification is reviewed, not inferred by a logical solver.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
basepath=R/'evidence/recount4-20261026/Rc4_premises.json'
before=json.loads(basepath.read_text()); plan=json.loads((P/'Rc5_audit_plan.json').read_text())
logs={}; evidence=[]; catalog={}
for a in plan:
 d=P/a['attempt'];r=json.loads((d/'receipt.json').read_text())
 assert r['exit_status']==0,a
 log=(d/'stdout.log').read_text(); assert not re.search(r'\berror(?:\(|:)',log),a
 name=a['module'].removeprefix('Rc5_Audit'); logs[name]=log
 evidence.append(dict(**a,source_sha256=sha(R/'lean'/(a['module']+'.lean')),stdout_sha256=sha(d/'stdout.log')))
 for block in re.split(r'(?=^structure )',log,flags=re.M):
  if not block.startswith('structure ') or 'fields:\n' not in block:continue
  key=re.match(r'structure (\S+)',block)[1]
  fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
  catalog[key]=dict(audit=name,fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
# Fresh unchanged trusted/interface inventories, not just a copied count.
oldcat=json.loads((R/'evidence/recount4-20261026/Rc4_field_catalog.json').read_text())
unchanged=[]
for k in oldcat.keys()&catalog.keys():
 assert catalog[k]['fields']==oldcat[k]['fields'],('changed atomic structure',k)
 unchanged.append(k)
assert len(unchanged)>=15,len(unchanged)
root=logs['Composition'].split('@AspisR1.Rc5_Top.deployed :',1)[1].split('@AspisR1.CPH_Top.deployed :',1)[0]
for s in ['F3T_CanonicalJoin.AcceptedVerifierJoin','F3T_Runtime.StoredCarrierBinding','CPH_Game.DeployedPairExecution','CPR_DataPersistence.TwoTransactionLaw','Rc5_Result.Outcome','CPH_Protection.Facts','CPH_Trace.Facts','CPH_Recorder.Facts']:
 assert s in root,s
assert 'Port1_CanonicalJoin.AcceptedVerifierJoin' not in root
assert 'OraclePortRuntimeBindingC7.StoredCarrierBinding' not in root
for s in ['@AspisR1.Rc4_Top.deployed','@AspisR1.SAF_Deployed.deployed','@AspisR1.Rc5_ResultForget.forget']:
 assert s in logs['Composition'],s
for s in ['TxS_Encoding.Facts','TxS_RawPublic.Facts','NP6_Constructors.Contents','∃ version','version.events = events','Rc5_Nonvacuity.Facts']:
 assert s in logs['Result'],s
caller=logs['Continuation'].split('def AspisR1.Rc5_Cont.Outcome',1)[0]
assert 'S2X.CheckpointVersionBinding' not in caller
assert 'S2W_AuthenticatedInputs.P2Prime' in caller
assert 'S2W_ChildJoins.FirstEntryVerifierConeJoin' in caller
assert '∀ (ports :' not in logs['Literal'] and '∀ (queryLeaves :' not in logs['Continuation']
finish=logs['Finish'].split('structure AspisR1.RowFinish_Control.RoundValues',1)[0]
assert '∃ r0 r1 weights pair dot' in ' '.join(finish.split()) or '∃' in finish
assert 'SAF_ReducedLaws.Arithmetic' in finish
for s in ['matches_S4_S7','semantic_S3_S9','dot_S5']:
 assert s in (R/'lean/SAF_C_SAF_FinishPrepared.lean').read_text(),s
arith=catalog['AspisR1.SAF_ReducedLaws.Arithmetic']
assert [s.rsplit('.',1)[1] for s in arith['field_names']]==['round0','round1','pair']
assert len(catalog['AspisR1.Port4D_Pairing.RoundLaws']['field_names'])==3
assert len(catalog['AspisR1.CPH_Game.DeployedPairExecution']['field_names'])==4
assert len(catalog['AspisR1.CPG_Projection.Observations']['field_names'])==9
# Source checks distinguish input guards from constructed output witnesses.
top=(R/'lean/Rc5_Top.lean').read_text(); close=(R/'lean/Rc5_Close.lean').read_text()
assert 'prepareOwner' not in top and 'primitiveOwner' not in top
assert 'Rc5_Source.source' in top and 'Rc5_Close.from_saf' in top
assert 'CPH_Protection.derive' in top and 'CPH_Trace.derive' in top and 'CPH_Recorder.physical' in top
assert 'let version := CPG_History.on_cuts' in close
assert 'yes version p2prime' in close and 'nonvacuity version' in close
assert 'rfl rfl version caller' in close
assert 'tx2,calls,encoding,base,initial,selected' in close
history={'L094','L095','L096','L180'}|{f'Rc2_P{i:03}' for i in range(1,6)}
finishRemoved={f'L{i}' for i in range(110,122)}|{'L125','L127','L128','L139','L140','L141','L148'}
assert len(history)==9 and len(finishRemoved)==19 and not history&finishRemoved
byid={r['id']:r for r in before['rows']};removed=history|finishRemoved
assert removed<=byid.keys()
assert byid['L180']['scope']=='deployment alias'
assert sum(byid[i]['scope']=='actual antecedent' for i in history)==8
assert all(byid[i]['scope']=='actual antecedent' for i in finishRemoved)
saf=json.loads((R/'evidence/finish-laws-20261026/SAF_premises.json').read_text())
assert finishRemoved=={r['id'] for r in saf['diff'] if r['change']=='removed'}
cph=json.loads((R/'evidence/cp-game2-20261026/CPH_LEDGER_DELTA.json').read_text())
assert history==set(cph['rows']) and len(cph['expanded_game'])==11
rows=[];diff=[]
def tag(r):
 i=r['id']
 if i=='L099':return 'PFin_'
 if i in {'L157','L159','L165','L181','L182','L185'}:return 'F3X_'
 if i in {f'L{n}' for n in range(195,200)}:return 'P6C_'
 if r['owner']=='session A' and r['scope']=='actual antecedent':return 'SAG_'
 if i in {'L083','L084','L097','L098'}:return 'JFx_'
 return 'UNCOVERED'
safrows={r['id']:r for r in saf['rows']}
for old in before['rows']:
 r=dict(old)
 if r['id'] in removed:
  reason=(cph['rows'][r['id']]['after'] if r['id'] in history else next(d['reason'] for d in saf['diff'] if d['id']==r['id']))
  theorem=('Rc5_Close.from_saf / CPH_Protection.derive' if r['id'] in history else 'Rc5_Source.source / Rc5_Literal.strengthen / SAF_Deployed')
  diff.append(dict(**r,change='removed',reason=reason,theorem=theorem));continue
 r.update(status='retained',running_job=tag(r),evidence='Rc5 fresh kernel inventories025–060; checked same-cut composition and reverse transport')
 r['owner_waits']=['No owner decision pending; implement or instantiate the retained boundary']
 if r['id'] in safrows and r['running_job']=='SAG_':r['blocker']=safrows[r['id']]['blocker']
 if r['id'] in {'L157','L159'}:
  r['name']='frozen3 '+r['name']
  r['blocker']='Retained exact frozen3 accepted log join / stored runtime carrier association at the combined selected dictionary. F3X_ must replace the raw join with its charged-collision route and bind the actual experiment, including rejected query prefixes.'
 if r['id'] in {'L165','L181','L182','L185'}:
  r['blocker']='Frozen3 is adopted and numerically composed. Complete physical-source/oracle/model/deployed-event transport is still required; no F3X_ result is imported here.'
 if r['running_job']=='JFx_':
  r['blocker']='JFx_ covers joint fixture instantiation of this retained accepted-event/P2Prime condition on the SAME dictionary and game instance; a fixture is not universal discharge of this family.'
 if r['id']=='L186':r['blocker']='Bind the combined selected SDK/key/clone/query/geometry/circle/native extraction dictionary to the frozen default/devnet/Pool artifacts; inherited exact-ELF success is not universal source lowering.'
 if r['id']=='L187':r['blocker']='Focused coherent-cache composition only; no full frozen release dependency replay in this task.'
 if r['id']=='L188':r['blocker']='Rc5 standard-axiom audit is complete; the final release-wide trust/axiom audit remains.'
 if r['id']=='N118':r['blocker']='Retained query budget now ranges over actual saved/post-copy heap/final allocator state in approved GExq adaptive second choice; one quantified family, no extra independence assumption.'
 rows.append(r);diff.append(dict(**r,change='changed' if r['id'] in {'L157','L159','N118'} else 'retained'))
newtrust=dict(id='Rc5_T001',name='RuntimePersistence',classification='T',owner='external',scope='actual antecedent',role='runtime trust',status='added',running_job='UNCOVERED',blocker='Approved byte-only CPR_DataPersistence.TwoTransactionLaw; retained named trust, not a Lean axiom',evidence='Rc5_Top input; audit057')
rows.append(newtrust);diff.append(dict(**newtrust,change='added'))
for n,(name,meaning) in enumerate(cph['expanded_game'].items(),1):
 r=dict(id=f'Rc5_G{n:03}',name='game.'+name,meaning=meaning,classification='P',owner='lead',scope='actual antecedent',role='approved game domain',status='added',running_job='JFx_',blocker='Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure.',evidence='Fresh field inventory056; exact CPH four-field game; expanded conjunct correspondence')
 rows.append(r);diff.append(dict(**r,change='added'))
def counts(rs):
 return dict(rows=len(rs),classes={c:sum(r['classification']==c for r in rs) for c in ['T','P','C']},by_owner={o:{c:sum(r['owner']==o and r['classification']==c for r in rs) for c in ['T','P','C']} for o in ['lead','session A','external']})
summary={s:counts([r for r in rows if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
summary['all retained audit rows']=counts(rows)
summary['deduplicated actual plus non-alias deployment']=counts([r for r in rows if r['scope']!='deployment alias'])
summary['actual excluding approved game domain']=counts([r for r in rows if r['scope']=='actual antecedent' and r.get('role')!='approved game domain'])
summary['deduplicated excluding approved game domain']=counts([r for r in rows if r['scope']!='deployment alias' and r.get('role')!='approved game domain'])
assert summary['actual antecedent']['classes']==dict(T=83,P=33,C=0)
assert summary['actual excluding approved game domain']['classes']==dict(T=83,P=22,C=0)
assert summary['deduplicated actual plus non-alias deployment']['classes']==dict(T=89,P=46,C=0)
assert summary['deduplicated excluding approved game domain']['classes']==dict(T=89,P=35,C=0)
assert summary['all retained audit rows']['classes']==dict(T=89,P=48,C=0)
result=dict(actual_theorem='AspisR1.Rc5_Top.deployed',baseline=before['actual_theorem'],baseline_path=str(basepath.relative_to(R)),baseline_sha256=sha(basepath),method=__doc__,statement_evidence=evidence,unchanged_fresh_structure_inventories=sorted(unchanged),counts=summary,before_counts=before['counts'],removed_actual_P=27,removed_alias_P=['L180'],removed_targeted_CPH=sorted(history),removed_targeted_SAF=sorted(finishRemoved),added_actual_T=1,added_game_P=11,net_actual_P_delta=-16,net_actual_T_delta=1,rows=rows,diff=diff,remaining_P_by_running_job=dict(Counter(r['running_job'] for r in rows if r['classification']=='P')),caveat='Approved game domain expanded and counted; no collapse of eleven clauses into one. CPH nine includes L180 deployment alias, so actual implementation-family removal is27, not28. Frozen3 raw join/runtime binding retained; full joint fixture and release target remain open.')
(P/'Rc5_premises.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
(P/'Rc5_field_catalog.json').write_text(json.dumps(catalog,indent=2,ensure_ascii=False)+'\n')
lines=['# Remaining P rows on Rc5_Top','','Tags denote running-job scope, not imported closure. JFx_ tags on success/P2Prime/game mean joint fixture instantiation, not universal discharge. Approved game conditions are counted as P here; the obligation-only subtotal excludes them explicitly.','','| ID | Scope | Owner | Job | Family | Blocker |','|---|---|---|---|---|---|']
for r in rows:
 if r['classification']=='P':lines.append('| '+' | '.join(str(r.get(k,'')).replace('|','/').replace('\n',' ') for k in ['id','scope','owner','running_job','name','blocker'])+' |')
(P/'Rc5_REMAINING.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(counts=summary,removed_actual_P=27,retired_alias_P=1,new_game_P=11,new_runtime_T=1,coverage=result['remaining_P_by_running_job']),indent=2))
