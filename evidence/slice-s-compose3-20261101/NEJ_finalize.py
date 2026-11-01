"""Derive all final statuses from checked packet; never hand-edit a CLOSED row."""
from pathlib import Path
import json,hashlib,copy,subprocess
import NEJ_validate as v
E=v.E;R=v.R;read=v.read
base=read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');packet=read(E/'NEJ_LEDGER_DELTA.json');review=read(E/'NEJ_REVIEWED_CERTIFICATES.json');out=v.compose(base,packet,review)
summary=v.summary(out);(E/'NEJ_VALIDATION_SUMMARY.json').write_text(json.dumps(summary,indent=1)+'\n')
spec=read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S'];by={f:[r for r in out['rows'] if r['function']==f] for f in spec['functions']}
edges=read(E.parent/'slice-s-compose2-20261029/NEE_EDGES.json')
for x in edges['edges']:
 edge=x['edge'];c=packet['edges'].get(edge);closed=v.certificate(c,edge,base,review)
 x.update(status='CLOSED' if closed else 'OPEN',certificate=c['id'] if closed else None)
 if closed:x['obstacle']=None
 elif all(r['composed_status']=='CLOSED' for r in by.get(x['callee'],[]) or [{'composed_status':'OPEN'}]):
  x['NEJ_additional_evidence']='Callee standalone row is now CLOSED; this exact caller edge remains OPEN on same argument/carrier/prestate/Result/ordered-effect transport. Standalone closure does not discharge its incoming call sites.'
 if x['callee'].endswith('::encode_common'):
  x['NEJ_additional_evidence']='Ten write windows have paired static-free native checks and KMX/array frame composition. Whole child-instance binding still needs selected digest-child frame/physical laws and actual parent call-site transport; no whole native child contract is inferred.'
assert {x['edge'] for x in edges['edges']}==set(spec['internal_edges'])
edges['NEJ_method']='NDT invariants unchanged; same-call certificates and rule-B loops checked; NativeContractSemanticTransport is P6/D188 option A reclassification'
(E/'NEJ_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
old=read(E.parent/'slice-s-compose2-20261029/NEE_STOP_AUDIT.json');members=[]
closed_functions={f for f,rs in by.items() if all(r['composed_status']=='CLOSED' for r in rs)}
for x in old['members']:
 f=x['function'];x=copy.deepcopy(x);x['composed_status']='CLOSED' if f in closed_functions else 'OPEN'
 if f in closed_functions:
  x.update(why_no_further_attempt='Standalone result/domain/frame certificate accepted by NEJ validator. Incoming caller edges still require their own certificates.',native_obligation='None for this standalone selected row.',lean_obligation='No remaining standalone Lean obligation; do not reprove unchanged accepted theorem.')
 elif not x['first_root_conservative_dependency']:
  x.update(why_no_further_attempt='Binding first-root order: validator remains OPEN. No other root started. Its exact retained names/edges below are unchanged.',native_obligation=x['native_obligation'])
 else:
  if f.endswith('StatementV1::common'):
   exact='K038/K039 pass/fail the actual getter and empty frame. Borrowed-interface admission remains unavailable: predecessor NEE_K039 failed codegen for Arbitrary<&Common>. No same-domain semantic unimplied control exists; pure Lean cannot fix Kani reference-return codegen.'
  elif f.endswith('::encode_common'):
   exact='K005..010 and K014..027 give paired scalar/one-iteration write support; L002/L004/L006/L007/L008 prove model/frame/disjointness join. Selected digest-child native frame/physical instance and parent call-site association are still missing. Model-only equality cannot create those native certificates.'
  elif f.endswith('::pool_v1_pair_forest_output_lane_v1'):
   exact='Final K050 caller oracle draft failed compilation on missing M31 import. Corrected generator is UNRUN after 50/50 Kani. Needs a valid positive, matched negative, full Result/ordered calls and child-instance binding. No new native caller credit.'
  elif f.endswith('::encode_pool_v1_pair_late_public_statement_v1'):
   exact='K040..049 pair the first five header writes. Fill, remaining header/afterstate writes, snapshot/afterstate child framed instances, and same-run Result/ordered-error-prefix composition still need native checks. Cannot infer full native frame from header windows.'
  elif f.endswith('::validate_pool_v1_pair_forest_terminal_statement_v1'):
   exact='Ruling-y caller support K052/K053 and NEE reached-only MODEL substitution are retained. Concrete payment_bridge, output_lane_bridge and late_bridge instances with complete native frames/physical bindings remain OPEN. No root theorem with only allowed hypotheses exists.'
  else:
   exact='Selected model equality and source pins are reused as listed below. The remaining actual native full-frame/physical instance and same-call source association are absent; all model-only transport would retain that exact native premise. Further native work requires Kani, now 50/50 consumed.'
  x.update(why_no_further_attempt=exact,native_obligation=exact,lean_obligation='No independent unproved MODEL conclusion has been identified beyond the reused source matches and new same-run frame/loop laws. The retained edge statement below needs the actual native certificate first; assuming its equality as a new Lean premise would not discharge it.')
 members.append(x)
audit=dict(slice='S',kani_used=50,kani_authorized=50,lean_used=len(list(E.glob('NEJ_L*/receipt.json'))),lean_authorized=120,first_root=old['first_root'],composed_rows_closed=summary['slice_closed'],root_closed=0,reason_for_under80percent_lean_stop='Kani exhaustion was followed by a new same-execution canonicality result-plus-frame induction, a fixed-length external-domain discharge, and the final axioms audit. This closed four more rows (14 total). Remaining members are enumerated individually: native frame/control/physical-source obligations cannot be proved by another model equality, while the six later roots are barred by the binding first-root order. This is an incomplete target, not a claim that 120 Lean attempts were spent.',members=members)
assert {x['function'] for x in members}==set(spec['functions'])
(E/'NEJ_STOP_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
# Check baseline bridge/source/trust fields are never promoted.
protected=['bridge_status','selected_claims','source_claim_text','frozen_body_verified','open_transitive_dependencies']
for a,b in zip(out['rows'],base['rows']):assert all(a.get(k)==b.get(k) for k in protected)
(E/'NEJ_ROW_DELTA.json').write_text(json.dumps(dict(before=6,after=len(summary['slice_closed']),new_rows=sorted(set(summary['slice_closed'])-set(old['composed_rows_closed'])),root_rows_closed={f:sum(r['composed_status']=='CLOSED' for r in by[f]) for f in spec['roots']},trust_rows_unchanged=out['trust_rows']==base['trust_rows']),indent=1)+'\n')
print(json.dumps(dict(composed_rows=len(summary['slice_closed']),edges=len(edges['edges']),members=len(members))))
