import subprocess,hashlib
F='crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common'
THEOREMS=['NEQ_CommonDecode.substitution','NEQ_CommonDecode.result_state_effects','NEQ_UnwrapDomains.fixed_read_packet','NEQ_DecodeScalar.digest_word_domain']
PAIRS=[['NEQ_K102','NEQ_K103'],['NEQ_K102','NEQ_K104'],['NEQ_K102','NEQ_K105']]
def validate(c,expected,ledger,v):
 try:
  q=c['common_decode'];assert q['function']==F and q['pairs']==PAIRS
  assert q['method']=='ruling y exact frozen caller and complete same-record field/frame substitution'
  assert q['domain']=='every typed216-byte input, arbitrary raw words, complete rejected and returned Common records'
  assert q['inner_hypotheses_remaining']==[] and q['trust_classification']=='P6/D188 option A reclassification'
  assert all(v.native_pair(*p) for p in PAIRS)
  from NEQ_artifacts import native_support
  attempts=sorted({a for pair in PAIRS for a in pair});assert q['native_support']==native_support(attempts)
  for r in q['native_support']:v.inherited.artifact(r)
  assert [t['name'] for t in q['theorems']]==THEOREMS and all(v.inherited.theorem(t) for t in q['theorems'])
  for r in q['manifests']:v.inherited.artifact(r)
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+F.split('::')[0]],cwd=v.R,text=True);a=source.index('fn decode_common(');z=source.index('\n}',a)+2;b=source[a:z]
  assert q['frozen_body']==b and q['frozen_body_sha256']==hashlib.sha256(b.encode()).hexdigest()
  m=v.read(v.E/'NEQ_K102-common-decode.json');assert m['frozen_body']==b and m['all_typed_inputs'] and m['full_child_Results'] and m['all_output_keys_and_limbs']
  erased=m['instrumented_body'].replace('fn native(','fn decode_common(').replace('    f: &mut Frame,\n','').replace('child_digest(crate::atomic_statement::unwrap_fixed_slice(','decode_digest_canonical(crate::atomic_statement::unwrap_fixed_slice(').replace('        ),f)\n        .map_err','        ))\n        .map_err').replace('child_validate(common,f)?','validate_common(common)?')
  assert erased==b
  p=(v.E/'NEQ_K102-NEQ_native_contracts.patch').read_text()
  for s in ['fn child_digest(bytes:&[u8;32]','bytes.as_ptr()==f.bytes.as_ptr().wrapping_add(start)','let start=if f.calls==0{80}else{112}','c.pool[f.j]==f.bytes[8+f.j]','c.deployment_domain[f.j]==f.bytes[40+f.j]','c.anchor_sequence==sequence&&c.asset_id.0==asset','c.anchor_root[f.limb].0==a&&c.nullifier[f.limb].0==n','assert!(f.calls==2)','check_record(&c,&f)','f.calls==calls']:
   assert s in p,s
  assert q['full_Result'] and q['empty_external_modifies'] and q['ordered_effects']==[] and q['same_borrowed_digest_places']
  rs=[r for r in ledger['rows'] if r['function']==F];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={F}|{F+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{F+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o};assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
