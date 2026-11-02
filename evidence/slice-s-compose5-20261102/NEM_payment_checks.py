"""Payment encoder: rejection prefix, framed suffixes and reached-child law."""
import hashlib,json,subprocess,re
P='crates/aspis-statement/src/pool_v1/payment_relation.rs::'
CASES={
 'transfer':dict(function=P+'encode_pool_v1_private_transfer_public_v1',prefix=['NEM_K012','NEM_K013'],suffix=[['NEM_K016','NEM_K017'],['NEM_K018','NEM_K019']],fields=['recipient_commitment','change_commitment'],windows=[[152,32],[184,32]],frames=[['NEL_K018','NEL_K019'],['NEL_K020','NEL_K021']]),
 'withdrawal':dict(function=P+'encode_pool_v1_withdrawal_public_v1',prefix=['NEM_K014','NEM_K015'],suffix=[['NEM_K020','NEM_K021'],['NEM_K022','NEM_K023'],['NEM_K024','NEM_K025']],fields=['amount','destination_token_account','change_commitment'],windows=[[148,4],[152,32],[184,32]],frames=[['NEL_K022','NEL_K023'],['NEL_K024','NEL_K025'],['NEL_K026','NEL_K027']])}

def validate(c,expected,ledger,v):
 try:
  q=c['payment_encode_composition'];case=q['case'];spec=CASES[case];f=spec['function']
  assert q['function']==f and q['method']=='native rejection prefix and source-ordered KMX suffix frames'
  assert q['all_typed_inputs'] and q['full_Result_and_bytes'] and q['empty_external_modifies']
  assert q['trust_classification']=='P6/D188 option A reclassification'
  assert q['prefix']==spec['prefix'] and q['suffix']==spec['suffix'] and q['frames']==spec['frames']
  assert q['fields']==spec['fields'] and q['windows']==spec['windows']
  assert q['child_domains']=='all typed public/common records and all raw digests; validator acceptance only selects continuation'
  assert q['common_frame_subject']==P+'encode_common' and q['no_inner_native_hypotheses']
  assert v.native_pair(*spec['prefix']) and all(v.native_pair(*p) for p in spec['suffix'])
  L=v.R/'evidence/slice-s-compose4-20261101'
  assert all(v.native_pair(*p,folder=L,prefix='NEL_') for p in spec['frames'])
  from NEM_artifacts import native_support,ref
  required=native_support(spec['prefix']+[a for pair in spec['suffix'] for a in pair])
  for pair in spec['frames']:
   for a in pair:required += [ref(L/n) for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEL_native_contracts.patch',a+'-NEL_oracle.patch']]
  assert q['native_support']==required
  for r in q['native_support']:v.inherited.artifact(r)
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+f.split('::')[0]],cwd=v.R,text=True)
  name=f.split('::')[1];a=source.index('pub fn '+name+'(');z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  validate_name=name.replace('encode_','validate_',1)
  assert body.index(validate_name+'(public)?;')<body.index('let mut output = [0u8;')<body.index('encode_common(')
  projection='transfer_common' if case=='transfer' else 'withdrawal_common'
  assert projection+'(public),' in body
  assert 'POOL_V1_'+('PRIVATE_TRANSFER' if case=='transfer' else 'WITHDRAWAL')+'_STATEMENT_MAGIC,' in body
  assert 'PoolV1TransitionKind::'+('PrivateTransfer' if case=='transfer' else 'Withdrawal')+',' in body
  assert body.rstrip().endswith('Ok(output)\n}')
  assert body.count('encode_digest_canonical(&public.')==(2 if case=='transfer' else 1)
  assert body.count('.copy_from_slice(')==(2 if case=='transfer' else 3)
  assert '#[kani::proof]' in (v.E/(spec['prefix'][0]+'-NEM_native_contracts.patch')).read_text()
  # The prefix's continuation and every error variant are native, with the
  # same actual public receiver. The matched control corrupts its reply.
  for a in spec['prefix']:
   text=(v.E/(a+'-NEM_native_contracts.patch')).read_text()
   assert 'fn prefix(public:' in text and '{child(public,f)?;f.reached=true;Ok(())}' in text
   assert 'actual==f.reply && f.log==1 && f.reached==f.reply.is_ok()' in text
   assert 'core::ptr::eq(p,f.expected)' in text
  if case=='transfer':
   assert 'POOL_V1_CANONICAL_FEE.to_le_bytes()' in body
   assert 'pub const POOL_V1_CANONICAL_FEE: u32 = 0;' in source
  wanted=['NEM_PaymentFrame.'+case+'_reply','NEM_PaymentReached.payment_instance','NEM_PaymentReached.payment_reached']
  if case=='transfer':wanted+=['NEM_PaymentFrame.common_reserved']
  assert [t['name'] for t in q['theorems']]==wanted and all(v.inherited.theorem(t) for t in q['theorems'])
  rs=[r for r in ledger['rows'] if r['function']==f];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={f}|{f+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{f+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
