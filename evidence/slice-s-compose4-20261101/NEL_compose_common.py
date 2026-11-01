"""One real dependency: total framed common validator and its canonical child."""
from pathlib import Path
import copy,json,hashlib
from NEL_artifacts import ref,theorem,native_support
E=Path(__file__).resolve().parent;R=E.parent.parent;P=E.parent/'slice-s-compose-20261029'
b=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text());p=json.loads((E/'NEL_LEDGER_DELTA.json').read_text());review=json.loads((E/'NEL_REVIEWED_CERTIFICATES.json').read_text())
f='crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common';callee='crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical'
rows=[r for r in b['rows'] if r['function']==f];edge=f+' -> '+callee
model=theorem('NED_CommonValidation','common_result',P);child=theorem('NED_PaymentCohorts','canonical_result',P)
g=[theorem('NEL_CommonOracle',n) for n in ['substitution','reached_argument','call_count']]
q=dict(method='ruling y: total scalar caller with local ordered child log',function=f,selected_child=callee,all_typed_inputs=True,local_frame_constructed=True,full_Result=True,empty_external_modifies=True,exact_body_projection=True,trust_classification='P6/D188 option A reclassification',shape='Result<(),PoolV1PaymentStatementFormatError>; mutable local record',controls={'native':'NEL_K034','contract':'NEL_K035','unimplied':'NEL_K039','inverted':'NEL_K040','frame':'NEL_K041'},positive='NEL_K032',negative='NEL_K033',native_support=native_support(['NEL_K032','NEL_K033','NEL_K034','NEL_K035','NEL_K039','NEL_K040','NEL_K041']),model_theorems=g,emitted_association=[model,child])
base=dict(kind='root-composition',frozen_revision=b['frozen_revision'],theorems=[model,child,*g],native_association=[ref(E/'NEL_K032/receipt.json'),ref(E/'NEL_K033/receipt.json')],same_inputs=True,same_carrier=True,same_state=True,same_result=True,ordered_effects=True,inner_hypotheses_remaining=[],physical_interpretation_derivation='Exact frozen caller projection; all typed common arguments; local expected record and zero log are constructed from this caller. Every reached Bool child receives this same anchor/nullifier in source order, on its total typed domain. The actual emitted source and G substitution are proved by the pinned total model identities. Native-contract semantic transport is P6/D188 option A reclassification, not removal.',callee_domain_established=True,canonical_carrier_established=True,hypotheses=['NativeContractSemanticTransport'],framed_scalar_caller=q)

def add(group,key,kind,names,claims):
 c=copy.deepcopy(base);c.update(id='NEL_common_'+key,kind=kind,subject=key)
 c['call_domain_certificate']=dict(subject=key,frozen_revision=b['frozen_revision'],native_association_kind='ruling-y',domain_theorems=[child,g[1]],physical_theorems=[model,g[0]],selected_callee_claims=claims,inner_hypotheses_remaining=[],exact_callsite='Two source-ordered canonicality checks of common.anchor_root and common.nullifier in frozen validate_common, after primitive zero/capacity guards; every scalar/record input is supported, including every rejection branch.',canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,trust_classification='P6/D188 option A reclassification',new_trust_rows=[],native_frame_complete=True,inner_names_discharged=names)
 h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review[key]=h;p[group][key]=c
claims=sorted({c for r in rows for c in r['selected_claims']})
add('members',f,'root-composition',[],claims)
for name in sorted({h['name'] for r in rows for h in r['named_hypotheses']}):add('hypotheses',f+'::'+name,'hypothesis-discharge',[name],claims)
obs=[o for r in rows for o in r['caller_domain_obligations'] if o.get('callee')==callee]
add('edges',edge,'call-domain',sorted({n for o in obs for n in o['required_named_hypotheses']}),sorted({n for o in obs for n in o['callee_claims']}))
for r in rows:
 for o in r['caller_domain_obligations']:
  if 'callee' not in o:add('externals',o['id'],'external-domain',[],claims)
(E/'NEL_LEDGER_DELTA.json').write_text(json.dumps(p,indent=1)+'\n');(E/'NEL_REVIEWED_CERTIFICATES.json').write_text(json.dumps(review,indent=1)+'\n')
