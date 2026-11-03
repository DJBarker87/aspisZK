import subprocess,hashlib
BASE='crates/aspis-statement/src/pool_v1/payment_relation.rs::'
FUNCTIONS={'transfer':BASE+'decode_pool_v1_private_transfer_public_v1','withdrawal':BASE+'decode_pool_v1_withdrawal_public_v1'}
PAIRS={'transfer':[['NEQ_K109','NEQ_K110'],['NEQ_K109','NEQ_K111'],['NEQ_K109','NEQ_K112']],'withdrawal':[['NEQ_K113','NEQ_K114'],['NEQ_K113','NEQ_K115'],['NEQ_K113','NEQ_K116']]}
ALTERNATIVES=['crates/aspis-core/src/field.rs::M31::to_le_bytes','crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes']
THEOREMS={case:['NEQ_PaymentDecode.'+case+'_substitution','NEQ_PaymentDecode.'+case+'_result_state_effects','NEQ_BorrowWidth.status','NEQ_BorrowWidth.fixed216','NEQ_UnwrapDomains.fixed_read_packet','NEQ_PaymentDomains.window_bounds']+(['NEQ_PaymentDomains.fee_primitive_width','NEQ_PaymentDomains.fee_zero'] if case=='transfer' else []) for case in FUNCTIONS}
def validate(c,expected,ledger,v):
 try:
  q=c['payment_decode'];case=q['case'];f=FUNCTIONS[case];assert q['function']==f
  assert q['method']=='ruling y exact byte caller; generic borrowed length guard and concrete nonzero-byte places; full Slice substitution'
  assert q['domain']=='every physically valid byte Slice; complete WrongLength prefix or same216-byte branch; no accepted-input assumption'
  assert q['inner_hypotheses_remaining']==[] and q['trust_classification']=='P6/D188 option A reclassification'
  assert q['pairs']==PAIRS[case]+[['NEQ_K118','NEQ_K119']] and all(v.native_pair(*p) for p in q['pairs'])
  from NEQ_artifacts import native_support
  attempts=sorted({a for pair in q['pairs'] for a in pair});assert q['native_support']==native_support(attempts)
  for r in q['native_support']:v.inherited.artifact(r)
  assert [t['name'] for t in q['theorems']]==THEOREMS[case] and all(v.inherited.theorem(t) for t in q['theorems'])
  for r in q['manifests']:v.inherited.artifact(r)
  v.inherited.artifact(q['guard_finding'])
  assert q['guard_shape']=='generic status only; valid Unit backing for all usize lengths; actual u8 success places checked separately'
  assert q['zst_pointer_identity_claimed'] is False and q['nonzero_byte_places_proved'] is True
  p=(v.E/'NEQ_K118-NEQ_native_contracts.patch').read_text();n=(v.E/'NEQ_K119-NEQ_native_contracts.patch').read_text()
  assert 'let backing=[();1];let length:usize=kani::any()' in p
  assert 'Result<&[();216],core::array::TryFromSliceError>' in p and 'actual.is_ok()==(length==216)' in p
  assert 'actual.is_ok()==(length==217)' in n and 'assert!(view.as_ptr()' not in p
  pos=PAIRS[case][0][0];source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+f.split('::')[0]],cwd=v.R,text=True);a=source.index('pub fn '+f.split('::')[1]+'(');z=source.index('\n}',a)+2;b=source[a:z]
  assert q['frozen_body']==b and q['frozen_body_sha256']==hashlib.sha256(b.encode()).hexdigest()
  m=v.read(v.E/(pos+'-payment-decode.json'));assert m['frozen_body']==b and m['full_child_Results'] and m['all_returned_fields'] and m['all_observed_bytes_and_limbs']
  erased=m['instrumented_body'].replace('fn native(','pub fn '+f.split('::')[1]+'(').replace('    f: &mut Frame,\n','').replace('child_common(bytes,f)?','decode_common(bytes)?').replace('child_digest(crate::atomic_statement::unwrap_fixed_slice(','decode_digest_canonical(crate::atomic_statement::unwrap_fixed_slice(').replace('        ),f)\n        .map_err','        ))\n        .map_err').replace('child_validate(&public,f)?','validate_pool_v1_'+('private_transfer' if case=='transfer' else 'withdrawal')+'_public_v1(&public)?')
  assert erased==b
  assert b.index('.try_into()')<b.index('require_header(')<b.index('let common = decode_common(bytes)?;')
  p=(v.E/(pos+'-NEQ_native_contracts.patch')).read_text()
  for s in ['fn child_common(bytes:&[u8;216]','core::ptr::eq(bytes,f.bytes)','fn child_digest(bytes:&[u8;32]','bytes.as_ptr()==f.bytes.as_ptr().wrapping_add(start)','p.pool[f.j]==c.pool[f.j]','p.deployment_domain[f.j]==c.deployment_domain[f.j]','p.anchor_sequence==c.anchor_sequence&&p.asset_id.0==c.asset_id.0','p.anchor_root[f.limb].0==c.anchor_root[f.limb].0&&p.nullifier[f.limb].0==c.nullifier[f.limb].0','p.change_commitment[f.limb].0==z','check_public(&p,&f)','expected==Err(e)','f.calls==calls']:
   assert s in p,s
  if case=='transfer':
   assert 'p.recipient_commitment[f.limb].0==r' in p and 'let start=if f.calls==1{152}else{184}' in p
   assert 'pub const POOL_V1_CANONICAL_FEE: u32 = 0;' in source
   assert q['resolved_alternatives']==ALTERNATIVES and q['primitive_fee_receiver']=='frozen u32 constant0;4-byte primitive to_le_bytes'
  else:
   assert 'p.amount==amount&&p.destination_token_account[f.j]==f.bytes[152+f.j]' in p and q['resolved_alternatives']==[]
  assert q['full_Result'] and q['empty_external_modifies'] and q['ordered_effects']==[]
  rs=[r for r in ledger['rows'] if r['function']==f];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={f}|{f+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{f+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o};assert expected in allowed
  if c['kind']=='alternative-resolution':assert case=='transfer' and expected in {f+' -> '+x for x in ALTERNATIVES}
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
