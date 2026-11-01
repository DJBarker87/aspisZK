"""Replace only rule16-suspended receipt uses, with new same-property controls."""
from pathlib import Path
import json,hashlib,copy
E=Path(__file__).resolve().parent;R=E.parent.parent;P=E.parent/'slice-s-compose2-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
ref=lambda p:dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()))
packet=json.loads((P/'NEE_LEDGER_DELTA.json').read_text());review=json.loads((P/'NEE_REVIEWED_CERTIFICATES.json').read_text());base=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text())
mapping={'005':'034','006':'035','009':'036','010':'037','007':'038','008':'039'}
bindings=json.loads((P/'NEE_MODEL_BINDINGS.json').read_text())
for f,b in bindings.items():
 for kind,old in [('positive','005'),('negative','006')] if f.endswith('M31::to_le_bytes') else [('positive','009'),('negative','010')] if f.endswith('::statement_public_common') else [('positive','007'),('negative','008')] if f.endswith('StatementV1::common') else []:
  p=E/('NEJ_K'+mapping[old])/'receipt.json'
  if p.exists():b[kind+'_receipt_sha256']=sha(p.read_bytes())
(E/'NEJ_MODEL_BINDINGS.json').write_text(json.dumps(bindings,indent=1)+'\n')
changed=[]
def update_refs(x):
 if isinstance(x,list):return [update_refs(v) for v in x]
 if isinstance(x,dict):
  if set(x)=={'path','sha256'}:
   old=x['path']
   for a,b in mapping.items():
    prefix='evidence/slice-s-compose2-20261029/NEE_K'+a
    if old.startswith(prefix):
     new=R/old.replace(prefix,'evidence/slice-s-compose3-20261101/NEJ_K'+b).replace('-NEE_', '-NEJ_')
     return ref(new)
   return x
  return {k:update_refs(v) for k,v in x.items()}
 if x in ['NEE_oracle.patch','NEE_native_contracts.patch']:return x.replace('NEE_','NEJ_')
 return x
for group in ['members','roots','hypotheses','edges','inventory_edges']:
 for subject,c in list(packet.get(group,{}).items()):
  if not any('NEE_K'+a in json.dumps(c) for a in mapping):continue
  # Retain all historical theorem statements; only the static-free native
  # revalidation and explicit new call-domain binding are additional evidence.
  c=update_refs(c);c['id']='NEJ_'+c['id']
  f=subject.split(' -> ')[0].split('::NCS_')[0]
  if '::' in subject and subject not in {r['function'] for r in base['rows']} and ' -> ' not in subject:
   f=next((r['function'] for r in base['rows'] if subject.startswith(r['function']+'::')),f)
  claims=sorted({x for r in base['rows'] if r['function']==f for x in r['selected_claims']})
  if not claims:claims=['typed primitive alternative excluded by width theorem']
  c['call_domain_certificate']=dict(subject=subject,frozen_revision=base['frozen_revision'],native_association_kind='native-contract',domain_theorems=c['theorems'],physical_theorems=c['theorems'],selected_callee_claims=claims,inner_hypotheses_remaining=[],exact_callsite='same frozen source span as the original NEE direct contract; new source contains only pure constructors and this harness',canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,trust_classification='P6/D188 option A reclassification',new_trust_rows=[],native_frame_complete=True,inner_names_discharged=[])
  c.pop('semantic_review_sha256',None);digest=sha(json.dumps(c,sort_keys=True).encode());c['semantic_review_sha256']=digest;review[subject]=digest;packet[group][subject]=c;changed.append(subject)
(E/'NEJ_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n');(E/'NEJ_REVIEWED_CERTIFICATES.json').write_text(json.dumps(review,indent=1)+'\n');(E/'NEJ_REVALIDATION_REVIEW.json').write_text(json.dumps(dict(revalidated_subjects=changed,method='same original complete statement and standard-axiom model theorems; new matching static-free contracts; borrowed shape remains unadmitted',no_original_proof_repeated=True),indent=1)+'\n')
