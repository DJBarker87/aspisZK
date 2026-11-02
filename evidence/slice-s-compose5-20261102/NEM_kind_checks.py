"""Call-site scalar certificates; original gates and bridge status stay active."""
import subprocess,hashlib
P='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::'
FUNCTIONS={'statement':P+'PoolV1PairForestTerminalStatementV1::transition_kind','payment':P+'PoolV1PairForestTerminalPaymentV1::transition_kind','parse':P+'transition_kind'}
PAIRS={'statement':[['NEM_K102','NEM_K103'],['NEM_K102','NEM_K108'],['NEM_K102','NEM_K109']],'payment':[['NEM_K104','NEM_K105']],'parse':[['NEM_K106','NEM_K107'],['NEM_K106','NEM_K110']]}
def validate(c,expected,b,v):
 try:
  q=c['kind_composition'];case=q['case'];f=FUNCTIONS[case];rs=[r for r in b['rows'] if r['function']==f]
  assert q['function']==f and q['all_typed_inputs'] and q['no_acceptance_precondition']
  assert q['method']=='actual getter/parser on same caller variant or byte, complete scalar frame, accepted enclosing-model association'
  assert q['trust_classification']=='P6/D188 option A reclassification' and q['inner_hypotheses_remaining']==[]
  assert q['native_pairs']==PAIRS[case] and all(v.native_pair(*p) for p in PAIRS[case])
  from NEM_artifacts import native_support
  aa=list(dict.fromkeys(a for pair in PAIRS[case] for a in pair));assert q['native_support']==native_support(aa)
  for r in q['native_support']:v.inherited.artifact(r)
  data=subprocess.check_output(['git','show',b['frozen_revision']+':'+f.split('::')[0]],cwd=v.R)
  assert q['frozen_bodies']==[data[r['frozen_body_byte_range'][0]:r['frozen_body_byte_range'][1]].decode() for r in rs]
  assert all(hashlib.sha256(x.encode()).hexdigest()==r['frozen_body_sha256'] for x,r in zip(q['frozen_bodies'],rs))
  wanted={'statement':'statement_window','payment':'payment_window','parse':'parser_result_frame'}[case]
  assert len(q['theorems'])==1 and q['theorems'][0]['name']=='NEM_KindInstance.'+wanted and v.inherited.theorem(q['theorems'][0])
  positive=(v.E/(PAIRS[case][0][0]+'-NEM_native_contracts.patch')).read_text()
  assert 'fn kind_call()' in positive and 'stub_verified' not in positive and 'copy_from_slice' not in positive
  if case=='parse':
   assert 'let bytes:[u8;320]=kani::any();let byte=bytes[5];let actual=transition_kind(bytes[5]);' in positive
   assert 'assert!(actual==expected' in positive and 'InvalidTransitionKind' in positive
  else:
   assert ('let kind=s.transition_kind();' if case=='statement' else 'let kind=p.transition_kind();') in positive
   assert 'output[5]=kind as u8;' in positive and 'if j==5{expected}else{old}' in positive
   assert 'let mut output:[u8;1880]=kani::any();' in positive
  allowed={f}|{f+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{o['id'] for r in rs for o in r['caller_domain_obligations']}
  assert expected in allowed
  if c['kind']=='external-domain':
   call=next(o for r in rs for o in r['caller_domain_obligations'] if o['id']==expected)['call']
   assert call.get('expression',call.get('syntax')) in ['Ok','Err']
  return True
 except (KeyError,AssertionError,OSError,ValueError,TypeError):return False
