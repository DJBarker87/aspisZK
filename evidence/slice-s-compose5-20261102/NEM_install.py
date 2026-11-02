"""Install explicitly reviewed new certificates without altering original gates."""
from pathlib import Path
import json,hashlib,copy
from NEM_artifacts import ref
E=Path(__file__).resolve().parent;R=E.parent.parent

def install(f,field,q,theorems,native,domain,physical,derivation,skip=(),alternatives=()):
 b=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text());p=json.loads((E/'NEM_LEDGER_DELTA.json').read_text());review=json.loads((E/'NEM_REVIEWED_CERTIFICATES.json').read_text())
 rows=[r for r in b['rows'] if r['function']==f];assert rows
 base=dict(frozen_revision=b['frozen_revision'],theorems=theorems,native_association=native,same_inputs=True,same_carrier=True,same_state=True,same_result=True,ordered_effects=True,inner_hypotheses_remaining=[],physical_interpretation_derivation=derivation,callee_domain_established=True,canonical_carrier_established=True,hypotheses=['CompositionTrustOptionA'],**{field:q})
 def add(group,key,kind,names,selected):
  c=copy.deepcopy(base);c.update(id='NEM_'+key,kind=kind,subject=key)
  c['call_domain_certificate']=dict(subject=key,frozen_revision=b['frozen_revision'],native_association_kind='native-loop' if field=='digest_composition' else 'ruling-y',domain_theorems=domain,physical_theorems=physical,selected_callee_claims=selected,inner_hypotheses_remaining=[],exact_callsite=derivation,canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,trust_classification='P6/D188 option A reclassification',new_trust_rows=[],native_frame_complete=True,inner_names_discharged=names)
  h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review[key]=h;p[group][key]=c
 claims=sorted({v for r in rows for v in r['selected_claims']})
 add('roots' if f in p['roots'] else 'members',f,'root-composition',[],claims)
 for name in sorted({h['name'] for r in rows for h in r['named_hypotheses']}):add('hypotheses',f+'::'+name,'hypothesis-discharge',[name],claims)
 for callee in sorted({g for r in rows for g in r['canonical_callees']}):
  if callee in skip:continue
  obs=[o for r in rows for o in r['caller_domain_obligations'] if o.get('callee')==callee]
  add('edges',f+' -> '+callee,'alternative-resolution' if callee in alternatives else 'call-domain',sorted({v for o in obs for v in o['required_named_hypotheses']}),sorted({v for o in obs for v in o['callee_claims']}))
 for r in rows:
  for o in r['caller_domain_obligations']:
   if 'callee' not in o:add('externals',o['id'],'external-domain',[],claims)
 (E/'NEM_LEDGER_DELTA.json').write_text(json.dumps(p,indent=1)+'\n');(E/'NEM_REVIEWED_CERTIFICATES.json').write_text(json.dumps(review,indent=1)+'\n')
