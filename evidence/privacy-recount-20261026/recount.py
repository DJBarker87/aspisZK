"""Mechanical rendering of reviewed row dispositions; no prover invocation."""
from pathlib import Path
from collections import Counter
import json,re
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
rows=json.loads((ROOT/'evidence/privacy-ledger-20261026/premises.json').read_text())
R='R1Z.'
pure={37,40,41,43,44,49,50,60,235,236,239,240,260}
source_support={78:'fibre',231:'clone',247:'trace-value',255:'all-variant coefficients'}
effect_ops={4,14,15,22,23,129}
model_groups=[(43,44,'RomObserverBin.observerMap','definitional observer program/decision projections'),(48,60,'PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises','matching canonical Instance and public-equality guard; no deployed source assertion'),(61,63,'ProverCommitOwnedEndpoint.caller_law','fixed owned decoder'),(64,71,'ProverCommitCallerInstance.budgets + ProverCommitOwnedEndpoint.caller_law','CallerLaw is supplied for fixed owned decoder'),(72,72,'ProverCommitCallerInstance.fibres + ProverCommitOwnedEndpoint.caller_law','fixed owned decoder'),(73,73,'ProverCommitCallerInstance.exhaustion + ProverCommitOwnedEndpoint.caller_law','fixed owned decoder'),(74,77,'PrivacyR1AcctBasis.packing_laws','concrete basis; SAME existential a,b'),(78,81,'PrivacyR1AcctBasis.basis','concrete PackBasis.indep, SAME coefficients'),(82,85,'PhaseWireLog2Bin.batches','fixed ordered wire batches'),(88,88,'PhaseWireLog2Bin.ordered_log','canonical model, all witness/tape/challenges'),(90,91,'R0Z.FsStatement.bit','Boolean rational 0/1 bound'),(92,92,'ProverCommitObserverQueries19.real_bound','all branches and capped observer'),(93,129,'BuilderCanonical.admitted_of_spend','canonical embedded RspendPlus Instance; semantic fields DERIVED from its honest guard'),(155,160,'ProverCommitFixedObserver.self_join','identity MODEL coupling, not deployed RunJoin')]
for row in rows:
 n=int(row['id'][1:]);old=row['status'];status='OPEN';bucket='b';why='Complete deployed caller interpretation/native association remains absent; feeds V038, not discharged by a model/source helper.';ev='runjoin.txt';res=[];theorem=None
 if old=='model-proved':
  status='CLOSED-ON-RESEARCH';bucket=None
  lo,hi,t,scope=next(g for g in model_groups if g[0]<=n<=g[1]);theorem=(R+t if not t.startswith('R0Z.') else t)
  why='Complete original MODEL-scoped row: '+scope+'. Native association is separately V038/V152–V154.';ev='../privacy-ledger-20261026/readable-20002.log; ../privacy-ledger-20261026/consumers-20005.log; inputs/research/'
 elif old=='data':
  status='REDUCED';bucket=None;res=[row['definition']+' / '+row['name']];why='Data/definition inventory only; retained at exactly this parameter/projection, no proposition or deployed instance supplied.';ev='../privacy-ledger-20261026/readable-20002.log'
 elif old=='domain':
  status='REDUCED';bucket=None;res=['BuilderCanonical.Instance.property : BuilderSpendRelation.RspendPlus / '+row['name'].split('RspendPlus.')[1]];why='Original honest-domain guard carried by the subtype, not a newly removed premise or an existence proof.';ev='inputs/research/docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderCanonical.lean.txt'
 elif row['group']=='N':
  status='REDUCED';bucket=None;res=[row['definition']+' / '+row['name']];why='Explicit overlap, retained native cut field; same unresolved carrier/effect/operation laws as V165/V167 and dictionary rows. Not an independent gate.';ev='../privacy-ledger-20261026/native-cut-table.md'
 elif row['classification']=='T' and n not in {370,371}:
  status='REDUCED';bucket=None;res=[row['definition']+' / '+row['name']];why='Accepted external law remains a named hypothesis, not a standard-axiom-only theorem for native execution.';ev='../privacy-ledger-20261026/fields-20004.log'
 if row['group']=='O':
  op=int(re.match(r'op(\d+)',row['name'])[1]);res=['ProverRwFull.ExternalFuns.op'+str(op)]
  bucket='b' if op in effect_ops else 'a';ev='dict.txt; inputs/dict/docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/reach7/REACHABILITY.md'
  why=('Native IO/entropy/Drop world law needs the actual effect interpreter.' if bucket=='b' else 'Exact selected source callback/value law can be supplied before whole RunJoin; full native composition remains separate V165/V167.')
  if op in pure:
   status='CLOSED-ON-CANDIDATE';bucket=None;theorem='R1Z.PDict_'+('CodecDictionary' if op in {49,50} else 'PureDictionary')+'.op'+str(op)+'_installed';res=[]
   why='Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion.'
  elif op in {16,18,85}:
   status='REDUCED';bucket=None;theorem='R1Z.PDict_ReachCaller.op'+str(op)+'_irrelevant'
   res=['V045 deployed FSExperiments installation','V167 native caller/effect association'];why='This source callback is irrelevant to the complete extracted caller. Does NOT install a generic native operation/type, which is the broader original row. Seven erasures include four already-selected fields absent from original open99.'
  elif op in source_support:
   status='REDUCED';bucket=None;res=['V165 native representation','V167 native library/effect association'];why='rw candidate supplies '+source_support[op]+' source callback; inherited std/native-table interpretation and SAME-selector/native association remain. Not added to dictionary sibling selector by arithmetic on counts.';ev='rw.txt'
 if n in {152,153,154,163,164}:
  bucket='a';why='Concrete source-to-model equation can be attacked independently before complete deployed effect/RunJoin installation; generic composition does not prove it.';ev='rw.txt; inputs/research/';res=[row['definition']+' / '+row['name']]
 if n==36: res=['Coupling.meanR on SAME eventual concrete RunJoin.cp'];why='Product projection_cp proves this only for a proposed product carrier; no deployed rust/sampling datum or complete installed coupling.'
 if n==37: res=['PV_RunJoin_Endpoint.PV_RunJoin_Premises.uniform_V037'];why='Named sufficient product-carrier premise, uninstantiated; packaging is not a substantive reduction.'
 if n==38: res=['PV_RunJoin_Endpoint.PV_RunJoin_Premises.disclosed_V038','PV_RunJoin_Endpoint.PV_RunJoin_Premises.observerOracle_V038'];why='Conditional exact-view equivalence preserves original bad and observer. Both complete-view fields and actual native interpreter are missing; no full refinement.'
 if n==46:
  status='EVIDENCED';bucket=None;theorem='R1Z.PV_RunJoin_Source.observer_nonempty';why='Chosen existing R1Adv carrier inhabited; no theorem Nonempty rust.Adversary for arbitrary free rust. Native carrier identification retained in V045.';ev='runjoin.txt; inputs/runjoin/docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_Source.lean.txt'
 if n==47:
  status='EVIDENCED';bucket=None;theorem='R1Z.PV_RunJoin_CanonicalFixtures.mathematical_fibres';res=['PV_RunJoin_CanonicalFixtures.Association.transfer_public_V047','PV_RunJoin_CanonicalFixtures.Association.withdrawal_public_V047'];why='Two mathematical fixture fibres proved, sentinel discharged; native chosen-public/byte associations still explicit. Arbitrary x nonemptiness NOT proved.';ev='runjoin.txt; inputs/runjoin/docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_CanonicalFixtures.lean.txt; rebase-evidence/fixture-comparison.json'
 if n==270:
  bucket='a';why='Safe Formatter replacement/quotient can be developed independently; forbidden axiom route is not admissible. op85 independence does not install generic type27.';ev='dict.txt'
 if n in {341,342,343}:
  status='EVIDENCED';bucket=None;mode={341:'default',342:'devnet',343:'pool'}[n];ev='rebase-evidence/candidate/build-'+mode+'/comparison.json';why='Later candidate build at 3f9177b6477a8ae91d028139be2a9c555fc300e7 matches exact required ELF SHA and size; supersedes initial gate-status STOP. Measurement, no native proof.'
 if n in {344,345,370,371,373,374,396}:
  bucket='c';decision={344:'barrier: reserve quiet host for preregistered median gate',345:'barrier: quiet SAME-profile baseline/candidate comparison',370:'owner accept pinned compiler-preservation trust law',371:'DOITM V371: owner select/authorize CPU timing mode and latency trust',373:'inversion zero-boundary: owner settle reachable zero-domain handling; finish actual call-site audit',374:'barrier: quiet timing host; retain fixed preregistered experiment',396:'client bundle pin: owner signer/storage/install adoption and live publication receipt'}[n]
  why=decision+'. No complete gate/theorem yet.';res=[decision];ev='l3.txt' if n in {370,371,373,374} else ('client.txt' if n==396 else 'rebase-evidence/fixture-comparison.json')
 if n==372:
  status='EVIDENCED';bucket=None;why='Research evidence executable/compiler/flags/CPU pinned, DOITM supported but disabled; not the adopted final release binary.';ev='l3.txt'
 if 347<=n<=351:
  field={347:'v347_native_event_producer',348:'v348_joint_mask_count_tls_oracle',349:'v349_equal_circle_integration',350:'v350_query_abort_integration',351:'v351_part47_composition'}[n];res=['PV_L1_Premises.PV_L1_Premises.'+field];why='Named LOCAL callback obligation uninstantiated for native producer/history. Generic local-to-joint theorem is not a row reduction.';ev='l1.txt; inputs/l1/'
 if 352<=n<=369:
  res=['PV_L2_Premises.PV_L2_Premises.V'+str(n)];why='Complete SAME-cp native observable/source-to-simE law missing. Extracted reference value erasure and conditional field packaging do not close or substantively reduce whole row.';ev='l2.txt; inputs/l2/'
  if n==366: res+=['PV_L1_Premises.PV_L1_Premises.v366_joint_raw_input_coupling']
 if 392<=n<=395:
  status='EVIDENCED';bucket=None;why='Merged selected64 operational source and retained-key/attempt mapping/lifecycle tests plus four pinned-ELF runtime fixtures supplied. Universal event/effect laws and owner final client bundle adoption remain V045/V167/V396.';ev='client.txt; inputs/client/evidence/pv-client-20261026/runtime-02-public/acceptance.json'
 # Apply the SAME rubric to the old snapshot, rather than inventing old CLOSED counts from T/P/C.
 baseline=('CLOSED-ON-RESEARCH' if old=='model-proved' else 'REDUCED' if old in {'data','domain'} or row['group']=='N' or (row['classification']=='T' and n not in {370,371}) else 'OPEN')
 row.update(baseline_status=baseline,recount_status=status,dependency_bucket=bucket if status=='OPEN' else None,rationale=why,residual_fields=res,theorem=theorem,audit_evidence=ev)
rows.append(dict(id='V380-inversion',name='D197 all reached inversions / original L2 V380 alias',classification='P',group='L',baseline_status='NOT-IN-BASELINE',recount_status='OPEN',dependency_bucket='c',rationale='Owner inversion zero-boundary decision required. Also depends on actual native reached-call/slot enumeration and SAME headline coupling; classify c by owner-first precedence. LogUp nonzero theorem is partial only.',residual_fields=['PV_L2_Premises.PV_L2_Premises.V380_inversion'],theorem='R1Z.PV_L2_InversionQ.logup_operand (partial; NoPole/slot correspondence)',audit_evidence='l2.txt; inputs/l2/'))
def count(rs):
 return {'rows':len(rs),'classes':dict(Counter(r['classification'] for r in rs)),'statuses':dict(Counter(r['recount_status'] for r in rs)),'open_dependencies':dict(Counter(r['dependency_bucket'] for r in rs if r['recount_status']=='OPEN'))}
summary={'baseline':{'rows':399,'classes':dict(Counter(r['classification'] for r in rows[:-1])),'statuses':dict(Counter(r['baseline_status'] for r in rows[:-1]))},'existing399':count(rows[:-1]),'requested_V001_V380':count(rows[:380]),'recount_with_inversion':count(rows),'new_lean_invocations':0,'new_kani_invocations':0,'premises_removed':0}
(OUT/'rows.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n');(OUT/'totals.json').write_text(json.dumps(summary,indent=2)+'\n')
text=['# Per-row recount, 2026-10-26 (B)','','Original row statements/classes are retained verbatim in the ledger. This table gives the disposition of each complete row, its exact scope, residual field or theorem, and OPEN dependency. All namespaces are source declarations, not new proofs. `a` independent; `b` native caller/interpreter; `c` named owner decision. See METHOD.md for scope and precedence.','','| Row | Baseline → recount | OPEN bucket | Exact residual/theorem; reason | Evidence |','|---|---|---|---|---|']
for r in rows:
 detail='; '.join(([r['theorem']] if r.get('theorem') else [])+r['residual_fields'])+'. '+r['rationale']
 text.append('| '+r['id']+' | '+r['baseline_status']+' → '+r['recount_status']+' | '+(r['dependency_bucket'] or '—')+' | '+detail.replace('|','\\|')+' | '+r['audit_evidence']+' |')
(OUT/'ROWS.md').write_text('\n'.join(text)+'\n')
print(json.dumps(summary,indent=2))
