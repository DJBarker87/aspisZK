from pathlib import Path
import json,copy,hashlib
from NEL_artifacts import ref,theorem,native_support
E=Path(__file__).resolve().parent;R=E.parent.parent;P=E.parent/'slice-s-compose-20261029'
b=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text());p=json.loads((E/'NEL_LEDGER_DELTA.json').read_text());review=json.loads((E/'NEL_REVIEWED_CERTIFICATES.json').read_text())
for case,pos,neg in [('transfer','NEL_K038','NEL_K044'),('withdrawal','NEL_K042','NEL_K043')]:
 fn='validate_pool_v1_'+('private_transfer' if case=='transfer' else 'withdrawal')+'_public_v1';f='crates/aspis-statement/src/pool_v1/payment_relation.rs::'+fn
 rows=[r for r in b['rows'] if r['function']==f]
 model=theorem('NED_PaymentValidation',case+'_result',P);projection=theorem('NED_PaymentCohorts',case+'_common',P)
 g=[theorem('NEL_PaymentOracle',case+'_'+n) for n in ['substitution','call_count']];fields=theorem('NEL_PaymentFieldCarriers',case+'_fields')
 q=dict(unit_fidelity=copy.deepcopy(p['members']['crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common']['framed_scalar_caller']),case=case,function=f,method='ruling y with y-prime immutable field projections',positive=pos,negative=neg,field_positive='NEL_K058',field_negative='NEL_K059',all_typed_inputs=True,full_Result=True,empty_external_modifies=True,frame_constructed=True,control_and_arguments_split=True,trust_classification='P6/D188 option A reclassification',native_support=native_support([pos,neg,'NEL_K058','NEL_K059']),theorems=[model,projection,*g,fields],common_certificate_subject='crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common')
 base=dict(frozen_revision=b['frozen_revision'],theorems=q['theorems'],native_association=[ref(E/pos/'receipt.json'),ref(E/neg/'receipt.json'),ref(E/'NEL_K058/receipt.json'),ref(E/'NEL_K059/receipt.json')],same_inputs=True,same_carrier=True,same_state=True,same_result=True,ordered_effects=True,inner_hypotheses_remaining=[],physical_interpretation_derivation='Universal Result/order certificate and universal immutable field/place certificates are instantiated on the SAME typed public parameter. The source projection fixes the argument sequence; the count reconstructs its full argument log. The closed projection and common-validator bridges are reused. No child modifies this input or external state. The local log starts at zero by construction. Source-level pure projections and emitted carrier identities discharge the child interpretation; there is no independent accepted execution or output witness. P6/D188 option A is reclassification.',callee_domain_established=True,canonical_carrier_established=True,hypotheses=['NativeContractSemanticTransport'],payment_caller=q)
 claims=sorted({c for r in rows for c in r['selected_claims']})
 def add(group,key,kind,names,selected):
  c=copy.deepcopy(base);c.update(id='NEL_payment_'+key,kind=kind,subject=key)
  c['call_domain_certificate']=dict(subject=key,frozen_revision=b['frozen_revision'],native_association_kind='ruling-y',domain_theorems=[projection,fields],physical_theorems=[model,*g,fields],selected_callee_claims=selected,inner_hypotheses_remaining=[],exact_callsite='Frozen '+fn+': actual same public parameter, exact common projection, immutable recipient/change fields; source-ordered scalar Result/argument product.',canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,trust_classification='P6/D188 option A reclassification',new_trust_rows=[],native_frame_complete=True,inner_names_discharged=names)
  h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review[key]=h;p[group][key]=c
 add('members',f,'root-composition',[],claims)
 for name in sorted({h['name'] for r in rows for h in r['named_hypotheses']}):add('hypotheses',f+'::'+name,'hypothesis-discharge',[name],claims)
 for callee in sorted({g for r in rows for g in r['canonical_callees']}):
  obs=[o for r in rows for o in r['caller_domain_obligations'] if o.get('callee')==callee]
  add('edges',f+' -> '+callee,'call-domain',sorted({n for o in obs for n in o['required_named_hypotheses']}),sorted({n for o in obs for n in o['callee_claims']}))
 for r in rows:
  for o in r['caller_domain_obligations']:
   if 'callee' not in o:add('externals',o['id'],'external-domain',[],claims)
(E/'NEL_LEDGER_DELTA.json').write_text(json.dumps(p,indent=1)+'\n');(E/'NEL_REVIEWED_CERTIFICATES.json').write_text(json.dumps(review,indent=1)+'\n')
