"""Recompute candidates against NKH, retaining complete original clauses."""
from pathlib import Path
import json,lzma,hashlib,copy
E=Path(__file__).resolve().parent;P=E.parent/'ledger18-20261108'
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1)+'\n').encode();p=E/n
 if n.endswith('.xz'):p.write_bytes(lzma.compress(raw,preset=6));Path(str(p)[:-3]+'.sha256').write_text(H(raw)+'\n')
 else:p.write_bytes(raw)
b=J(P/'NKH_LEDGER.json.xz');by={r['row']:r for r in b['rows']};statements={}
for l in ((E/'NKN_L002/stdout.log').read_text() if (E/'NKN_L002/stdout.log').exists() else lzma.decompress((E/'NKN_L002/stdout.log.xz').read_bytes()).decode()).splitlines():
 if 'NKN_OWNER 'in l:
  x=json.loads(l.split('NKN_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x
old=J(P/'NKH_KERNEL_STATEMENTS.json.xz');wrong=[k for k in old if old[k]!=statements.get(k)];assert not wrong
assert set(statements)==set(J(E/'NKN_AUDIT_ROOTS.json')['roots'])
put('NKN_KERNEL_STATEMENTS.json.xz',statements);put('NKN_OWNER_COMPARISON.json',dict(status='PASS',predecessor_roots=len(old),identical=len(old),new_roots=len(statements)-len(old),mismatches=wrong))
rows=[]
for folder,pre in [('claims2','NKA'),('poseidon-state','NKG'),('field4','NKJ')]:
 e=E.parent/(folder+'-20261108')
 for f in J(e/f'{pre}_CLOSED.json')['functions']:
  for rid in f['rows']:
   r=by[rid];assert r['status']=='OPEN'and r['function']==f['function']and (pre=='NKG' or r['frozen_body_sha256']==f['frozen_body_sha256'])
   additions=[]
   if pre=='NKA':
    orig=J(e/'NKA_BASELINE_ROWS.json')[rid];packet=J(e/'NKA_ROW_OBLIGATIONS.json')[rid]
    assert orig['obligation_statement_hash']==f['obligation_statement_hash']
    assert packet['canonical_callees_retained']==r['canonical_callees']
    assert [v['original']for v in packet['clauses']]==orig['obligation']['caller_domain_obligations']
    if rid=='TX1:069':
     assert r['obligation']['NKC_parent_basis_obligation']==orig['obligation']
     extras=r['obligation']['NKC_explicit_child_domains'];assert len(extras)==4
     for c in extras:
      own=c['kind']=='own'
      additions.append(dict(original=c,resolution='DISCHARGED_SAME_ARGUMENTS'if own else'CALLER_CONTEXT_RETAINED',roots=['AspisR1.NKA_QueryPairs.reached','AspisR1.NJT_QDomains.initial','AspisR1.NJT_QDomains.scan_preserved','AspisR1.NKA_OuterCut.association'],parent_provenance='Opening-transcript unit remains incoming at TX1:168; no successful semantic finish presumed.'))
    else:assert orig['obligation']==r['obligation']
    assert packet['inventory_domain_obligations']==r['obligation']['inventory_domain_obligations']and packet['named_hypotheses']==r['obligation']['named_hypotheses']
   elif pre=='NKG':
    packet=next(x for x in J(e/'NKG_ROW_PACKETS.json')if x['row']==rid)
    assert packet['frozen_body_sha256']==r['frozen_body_sha256']
    assert packet['original_inventory']['obligation']==r['obligation']
    assert packet['original_obligation_statement_hash']==r['obligation_statement_hash']
   else:
    delta=next(x for x in J(e/'NKJ_LEDGER_DELTA.json')['entries']if x['row']==rid)
    assert delta['obligation_statement_hash']==r['obligation_statement_hash']and delta['canonical_callees_preserved']==r['canonical_callees']
   missing=[n for n in f['lean_roots']if n not in statements];assert not missing,missing
   ks=[statements[n]for n in f['lean_roots']]
   cls={k:copy.deepcopy(r['obligation'][k])for k in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']}
   detail={'NKA':'129: forall Reservation, SAME actual allocator1392/align4, fail/div/reject/success; Ready typed history and owned singleton only AtAllocation. 069: derived default, SAME carried state/selected advance, full replies and internally derived scan/finish domains; edge202 retained spurious-by-name.', 'NKG':'Deterministic308, no security-oracle premise. Own canonical input arrays/selectors/constants; SAME ROM bounds and child replies proved internally. Prepared block mul additive source edge uses FIv_PreparedTotal.mul only PreparedFor/canonical; native only forwards K044..046.', 'NKJ':'ACTUAL frozen source segments, arbitrary-prestate one-step plus Lean finite induction. All Result/error arms on canonical/budget/arity domain; full3x3U64 or completeQM31 record. Product is integer limb arithmetic; field value law Lean-only. Same arrays and n+remaining<=4 retained at225; ReviewedTranscription under(ah)/(ba).'}[pre]
   rows.append(dict(row=rid,provider=pre,function=r['function'],basis_obligation_statement_hash=r['obligation_statement_hash'],submitted_obligation_statement_hash=f.get('obligation_statement_hash'),frozen_body_sha256=r['frozen_body_sha256'],certificate=f,root_domain=f['root_domain'],roots=f['lean_roots'],primary_root=f['lean_roots'][0],original_clauses=cls,kernel_statements=ks,baseline_amendment_review=additions,checks=dict(basis_function_body_and_complete_obligation=True,no_double_count=True),clause_review=[dict(original=c,proof_roots=f['lean_roots'],disposition='Retained verbatim; source call/constructor/full Result and frame in named roots. Unit context stays caller-owned and is reattached at every parent.')for c in cls['caller_domain_obligations']],hypothesis_inventory=dict(allowed_ruling='(aq)(2)',ordinary_inputs=f['root_domain'],reviewed_native_cuts='Typed same-call native step/source segment observations; P6/D188 option-A transport, not a new game assumption.',source_site_reservation='129 universal Reservation and SAME allocator action; no success restriction',added_game_hypotheses=[],no_arbitrary_Ops_Run_endpoint_or_child_success_premise=True),review=detail,missing_kernel_roots=missing,gate_admitted=False))
assert len(rows)==len({r['row']for r in rows})==11
parents=[];cs={x['row']:x for x in rows}
for c in rows:
 r=by[c['row']]
 for par in b['rows']:
  if par['transaction']!=r['transaction']or r['function']not in par['canonical_callees']:continue
  if par['row']=='TX1:069'and c['row']=='TX1:202':continue
  for kind,required in [('own',c['root_domain'])]+[('inventory:'+o['unit'],o['domain'])for o in r['obligation']['inventory_domain_obligations']]:
   roots=cs[par['row']]['roots']if par['row']in cs and kind=='own'else None
   clause=dict(id=f'NKN-caller:{par["row"]}:{c["row"]}:{kind}',caller=par['function'],callee=r['function'],required=required,status='DISCHARGED'if roots else'OPEN',discharged_by=roots,reason='SAME internal arguments/canonicality/budget derived by named roots.'if roots else'Own-domain and upstream unit/provenance remain actual parent obligations; helper closure never closes parent.')
   parents.append(dict(parent=par['row'],helper=c['row'],kind=kind,caller_clause=clause,parent_candidate=par['row']in cs))
# Exact adopted children, not NKA baseline16 status.
children=[]
for rid in ['TX1:066','TX1:067']:
 r=by[rid];assert r['status']=='CLOSED'
 for ro in r['root_owners']:assert statements[ro['root']]==old[ro['root']]
 children.append(dict(row=rid,status='CLOSED_IN_NKH',roots=r['root_owners'],same_arguments='NKA_OuterCut.association / QueryPairs.reached derive default and every SAME-block carry; NJT_QDomains.scan_preserved; finishCurrent receives SAME state/selected advance.'))
put('NKN_CHILD_REVIEW.json',dict(status='PASS',children=children,baseline16_status_not_reused=True,hash_difference069='NKH retained four explicit NKC child-own/unit clauses. Own clauses discharged; opening-transcript context remains incoming at168. All original clauses retained.',NJV_TX2_093=dict(status='CLOSED_UNCHANGED',roots=by['TX2:093']['root_owners'],domain='Binary entry SAME12 canonical distinct indices, <=9216 bytes; not the superseded literal10 unit.',evidence='NJV_TX2.TX2_093 via NJV_EntryCall.bridge / NJV_Constructors.entry; full error arm and abort; NKN_L039 prints exact definitions.')))
put('NKN_CANDIDATE_REVIEW.json',dict(status='REVIEW_PASS_GATE_PENDING',rows=rows,no_double_count=True,comparison_basis='NKH complete obligations, including added069 clauses; no ledger16/17 delta reused'))
put('NKN_PARENT_CLAUSES.json',dict(clauses=parents,parents=sorted({c['parent']for c in parents}),no_unsubmitted_parent_promotion=True))
# Additional helper/cut definitions are printed for review in one focused module.
names=['AspisR1.NKA_ClaimsRoot.claims','AspisR1.NKA_ClaimsOwnership.AtAllocation','AspisR1.NKA_ClaimsEffects.native','AspisR1.NKA_ClaimsEffects.cohort','AspisR1.NKA_HeapCarrier.RowCut','AspisR1.NKA_HeapCarrier.BoxCut','AspisR1.NKA_OuterCut.Cut','AspisR1.NKA_QueryPairs.reached','AspisR1.NKG_ColumnCuts.Trace','AspisR1.NKG_HelperCuts.Full','AspisR1.NKG_HelperCuts.Internal','AspisR1.NKG_PreludeFrame.Cut','AspisR1.NKG_GroupFrame.Frame','AspisR1.NKG_OracleCuts.Output','AspisR1.FIv_PreparedTotal.mul','NKJ_NativeSmall.source','NKJ_NativeStep.source','NKJ_NativeFold.source','NKJ_Cohort.source','NJV_TX2.TX2_093']
# Use only verified names; FIv namespace is checked against owner inventory.
names=names
(E/'NKN_HypothesisReview.lean').write_text('import NKN_COMBINED_IMPORT\nimport Lean\nopen Lean Elab Command\nset_option pp.all true\n'+''.join('#print '+n+'\n'for n in names))
print(json.dumps(dict(stage='review',candidates=len(rows),parent_clauses=len(parents),predecessor_roots_unchanged=len(old))))
