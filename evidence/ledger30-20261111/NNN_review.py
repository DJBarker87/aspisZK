"""Review the five FIN instantiations and dispose caller clauses bottom-up."""
from pathlib import Path
import json,lzma,hashlib,copy,subprocess
E=Path(__file__).resolve().parent;R=E.parent;P=R/'ledger29-20261111';H=lambda b:hashlib.sha256(b).hexdigest()
def put(n,x): (E/('NNN_'+n+'.json')).write_text(json.dumps(x,sort_keys=True,indent=1)+'\n')
basis=json.loads(lzma.open(P/'NNM_LEDGER.json.xz').read());by={r['row']:r for r in basis['rows']}
assert basis['gate']=='PASS'and basis['counts']=={'CLOSED':594,'OPEN':5}
statements={}
for l in (E/'NNN_L007/stdout.log').read_text().splitlines():
 if l.startswith('NNN_OWNER '):
  x=json.loads(l[10:]);statements[x['root']]=x
assert len(statements)==9
put('KERNEL_STATEMENTS',statements)
raw=json.loads((R/'fin-host-20261108/NNO_audit/final/proof0.json').read_text());assert raw['exit_status']==0
rawby={x['root']:x for x in raw['results']};seed=json.loads((E/'NNN_SEED.json').read_text())
for p in (R/'fin-20261108').glob('*.lean'):
 receipt=json.loads((R/'fin-host-20261108'/('NNO_L'+str(15+['FIN_240','FIN_221','FIN_213','FIN_333','FIN_330','FIN_COMBINED_IMPORT'].index(p.stem)).zfill(3))/'receipt.json').read_text())
 assert receipt['source_hashes']['NNO_sources/'+p.name]==H(p.read_bytes())
 assert any(z['source'].endswith('/'+p.stem+'.olean')and z['source_sha256']==z['selected_sha256']for z in seed['copies'])
rows=[('TX2:240','FIN_240.candidate',['TX2:239','TX2:241']),('TX1:333','FIN_333.candidate',['TX1:344','TX2:240']),('TX2:221','FIN_221.candidate',['TX1:344','TX2:240']),('TX1:330','FIN_330.candidate',['TX1:331','TX1:333','TX1:344','TX2:240']),('TX2:213','FIN_213.candidate',['TX2:214','TX2:221','TX1:344','TX2:240'])]
parent=[]
oldclauses=json.loads((P/'NNM_CLAUSE_REVIEW.json').read_text());res241=next(x for x in oldclauses['clauses']if x.get('id')=='NLG-upstream:TX2:241:TX2:124:native-input');assert res241['status']=='DISCHARGED'
for row in ['TX2:240','TX2:221','TX2:213']:
 z=copy.deepcopy(next(x for x in oldclauses['clauses']if x.get('id')==f'NLG-upstream:{row}:TX2:124:native-input'))
 z.update(status='DISCHARGED',discharged_by='TX2:241',lean='NMX_R9_StageTwo.root',S2=res241['S2'],basis241_verbatim=res241);parent.append(z)
for x in oldclauses['registered_caller_clauses']:
 z=copy.deepcopy(x)
 if z['id'].endswith(':D1'):z.update(status='DISCHARGED_INTERNALLY',discharged_by='FIN_240.candidate',support='NMV_RslDomain.domain241 uses NMV_RslSnapshots.images_consistent on the SAME successful snapshot list')
 else:z.update(status='DISCHARGED_FOR_CHILD_WITH_OWN_INPUT_RETAINED',discharged_by='FIN_240.candidate',support="NMV_RslDomain.domain241 transports entry D2prime at SAME account[6]/[0] payloads; remains own-input clause of240")
 parent.append(z)
parent.append(dict(id='NNN-caller:TX2:240:D2prime',row='TX2:240',status='OPEN_CALLER_CLAUSE',callers=['TX1:333','TX2:221'],domain='RSL.TX2_240.Domain LIBB_V2Star.library = Root0 on SAME entry-state payloads of accounts[6]/[0]',discharged_for_child='NVR_Folds.process_tx1: own.2.1',owner='333/221 own-input P2'))
parent.append(dict(id='NNN-caller:TX1:333/TX2:221:Domain',rows=['TX1:333','TX2:221'],status='DISCHARGED_FOR_CHILD_WITH_OWN_INPUT_RETAINED',domain='RSL.TX2_221.Domain V (RSL.TX1_344.asStage1 VL P C): P1 admitted; P2 stage2 implies D2prime; P3 stage1 implies S1.dom',callers=['TX1:330','TX2:213'],discharged_by='NVR_Folds.entry_tx1 / entry_tx2 (rev4 re-pins of NNF_Folds.entry_tx1 / entry_tx2)',support='P1 from admitted guard, P2/P3 passed as E1/E2',source='evidence/fin-20261108/FIN_CALLER_CLAUSES.json'))
entry=dict(id='NNN-entry:TX1:330/TX2:213:Domain',rows=['TX1:330','TX2:213'],kind='ENTRY_OWN_INPUT_CLAUSE',status='CARRIED_TO_HEADLINE',owner='TOP:NMF_B (Root0 at the selected occurrence or E_rec) with TOP:R0rep',authority='RSL_INDEX item 1; rulings (bf)(2), (aq)(2), (bf)(3)',domain='TX2_213.Domain: E1 = D2prime on admitted ASQ8 route; E2 = True on stage1 route',discharged_by=None,blocks_CLOSED=False,prohibited_discharge=['hypothesis','TCK.domain213_weaken at canonical library','Root0 itself'])
parent.append(entry);put('PARENT_CLAUSES',dict(clauses=parent,entry_headline_inventory=entry,canonical241_Domain_verbatim=oldclauses['canonical241_Domain_verbatim']))
review=[];clausereview=[]
for row,name,children in rows:
 r=by[row];rb=rawby[name];assert set(rb['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}and rb['equal']
 c=dict(row=row,theorem=name,implementation=name.replace('candidate','producer')+' choices allocation',kernel_statement=statements[name],basis_obligation_statement_hash=r['obligation_statement_hash'],route='FIN merged instantiation; no NNN_Inst* duplication',canonical_children=[dict(row=n,status='CLOSED'if by[n]['status']=='CLOSED'else'PENDING_EARLIER_IN_THIS_GATE',roots=by[n]['root_owners'],same_arguments='literal producer; NNO_StatementChecks and NNN_InstalledChecks rfl')for n in children],current_raw_result=rb,raw_evidence='evidence/fin-host-20261108/NNO_audit/final/proof0.json',statement_checks='NNO_L023/stdout.log + NNO_StatementChecks unchanged object',install_checks='NNN_InstalledChecks f344_same/f240_same/process_same/entry_same',domain='D2prime'if row=='TX2:240'else'P1/P2/P3'if row in ['TX1:333','TX2:221']else'E1/E2',own_input=[x for x in parent if row in x.get('rows',[x.get('row',x.get('caller'))])],gate_admitted=False,gate_status='WAITING_FINAL_SCAN',source_chain='NNN_SOURCE_REVIEW.json',library='LIBB_PoolLib.library/deployed, LIBB_V2Star.library; LIB_Instances.VL/P/C',statement_data='universally quantified Choices and240 Allocation;344 uses SAME fixed NNG_Candidate344.allocation as ledger29; no new hypothesis')
 if row=='TX2:240':c['phantom_edge']=dict(callee='TX2:043',status='RECLASSIFIED_SPURIOUS_BY_NAME',edge_retained=True)
 if row in ['TX1:333','TX2:221']:c['same_function_pair']='RSL.TAS.row333_is_221, NNO_StatementChecks.tas333'
 if row in ['TX1:330','TX2:213']:c['same_function_pair']='RSL.TAS.row330_is_213, NNO_StatementChecks.tas330'
 review.append(c)
 for kind in ['caller_domain_obligations','inventory_domain_obligations']:
  for z in r['obligation'][kind]:
   disp='DISCHARGED_IN_COMPLETE_SOURCE_FOLD';proof=name
   if z.get('status')=='RECLASSIFIED_SPURIOUS_BY_NAME':disp=z['status'];proof=None
   elif z.get('id','').startswith('NLG-upstream:'):disp='DISCHARGED';proof='NMX_R9_StageTwo.root'
   elif z.get('id','').endswith(':D1'):disp='DISCHARGED_INTERNALLY';proof='NMV_RslSnapshots.images_consistent / NMV_RslDomain.domain241'
   elif z.get('id','').endswith(':D2'):disp='DISCHARGED_FOR_CHILD_WITH_OWN_INPUT_RETAINED'
   clausereview.append(dict(row=row,kind=kind,original=z,status=disp,discharged_by=proof,reason='Same-input complete fold. Constructor/std primitive laws and lifecycle/non-deployed branches are handled by emitted transports and admitted guard; entry/Root0 own-input clauses remain explicitly carried in NNN_PARENT_CLAUSES. Inventory U18 is a checklist; clock Err arm retained, no success-only claim.'))
put('CANDIDATE_REVIEW',dict(candidates=review,gate='PENDING',route='FIN',security_target_established=False))
put('CLAUSE_REVIEW',dict(clauses=clausereview,carried_ledger29_verbatim=oldclauses,parent_clauses='NNN_PARENT_CLAUSES.json',entry_headline_inventory=entry,TGB2=oldclauses['TGB_2'],TGB3=oldclauses['TGB_3'],U16='DISCHARGED_IN_COMPLETE_SOURCE_FOLD; scan/reconstruct items carried to242 unchanged',no_hypotheses_added=True))
for paths,rev in [(['crates','programs/r1-cost-probe','Cargo.lock'],'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),(['programs/aspis-pool'],'b936275465')]:
 assert not subprocess.check_output(['git','diff',rev,'HEAD','--',*paths]);assert not subprocess.check_output(['git','diff','HEAD','--',*paths])
put('FROZEN_SOURCE_CHECK',dict(status='PASS',source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',Pool='b936275465',ELFs=json.loads((P/'NNM_FROZEN_SOURCE_CHECK.json').read_text())['ELFs'],rebuild_trigger=False,ELF_claim='Inherited pins only; no shipped source change or rebuild'))
# Complete old/new rev4 source/object table from merged handoff (no re-pinning by this job).
put('REPIN_REUSE',dict(handoff='evidence/nvr-20261108/NVR_HANDOFF.md',handoff_sha256=H((R/'nvr-20261108/NVR_HANDOFF.md').read_bytes()),comparison=json.loads((R/'fin-host-20261108/NNO_STATEMENT_COMPARISON.json').read_text()),kernel_statements=json.loads((R/'fin-host-20261108/NNO_KERNEL_STATEMENTS.json').read_text()),rev1_exports_imported=False,selection='NNN_SEED.json / ledger29 coherent base + NNO exports'))
print('Five FIN candidates reviewed, clauses registered; no row credit before final scan')
