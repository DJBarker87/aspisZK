import hashlib,subprocess,re
F='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_result'
THEOREMS=['NEQ_ResultValidator.result_state_effects','NEQ_ResultValidator.result','NEQ_ResultValidator.call_shape','NEQ_ResultValidator.lane_domain','NEQ_ResultValidator.after_domain','NEQ_ResultValidator.ordered_effects']
def validate(c,expected,ledger,v):
 try:
  q=c['result_validator'];assert q['function']==F and q['method']=='ruling y exact frozen caller with local full-Result oracles and concrete substitution'
  assert q['domain']=='every typed Result record; no canonicality or successful child assumption'
  assert q['inner_hypotheses_remaining']==[] and q['trust_classification']=='P6/D188 option A reclassification'
  assert q['pairs']==[['NEQ_K044','NEQ_K045'],['NEQ_K044','NEQ_K046'],['NEQ_K044','NEQ_K047']]
  assert all(v.native_pair(*pair) for pair in q['pairs'])
  from NEQ_artifacts import native_support
  assert q['native_support']==native_support([f'NEQ_K{n:03}' for n in range(44,48)])
  for r in q['native_support']:v.inherited.artifact(r)
  assert [t['name'] for t in q['theorems']]==THEOREMS and all(v.inherited.theorem(t) for t in q['theorems'])
  for r in q['manifests']:v.inherited.artifact(r)
  p=(v.E/'NEQ_K044-NEQ_native_contracts.patch').read_text();assert 'stub_verified' not in p
  for text in ['core::ptr::eq(d,&f.expected.nullifier)','core::ptr::eq(a,&f.expected.verified_afterstate)','after:Result<[u8;688],PoolV1PairVerifierTransportErrorV1>','lane:Result<u8,PoolV1PairForestAccountErrorV1>','let actual=native(&r,&mut f)','actual==expected','f.calls==if after_reached{2}else if reached{1}else{0}']:
   assert text in p,text
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+F.split('::')[0]],cwd=v.R,text=True);a=source.index('fn validate_result(');z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  m=v.read(v.E/'NEQ_K044-result-validator.json');assert m['frozen_body']==body and m['all_typed_inputs'] and m['full_lane_and_after_Results']
  erased=m['instrumented_body'].replace('fn native(','fn validate_result(').replace('    frame: &mut Frame,\n','').replace('lane(&result.nullifier,frame)','pool_v1_pair_forest_output_lane_v1(&result.nullifier)').replace('after(&result.verified_afterstate,frame)','encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)')
  assert erased==body
  assert q['full_Result'] and q['ordered_effects'] and q['empty_external_modifies']
  rs=[r for r in ledger['rows'] if r['function']==F];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={F}|{F+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{F+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
