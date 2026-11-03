import subprocess,hashlib,re
FUNCTIONS={'header':'crates/aspis-statement/src/pool_v1/payment_relation.rs::require_header','m31':'crates/aspis-core/src/field.rs::M31::from_le_bytes','digest':'crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical'}
PAIRS={'header':[['NEQ_K087','NEQ_K088'],['NEQ_K087','NEQ_K089']],'m31':[['NEQ_K090','NEQ_K091'],['NEQ_K090','NEQ_K092']],'digest':[['NEQ_K093','NEQ_K094'],['NEQ_K093','NEQ_K095']]}
THEOREMS={'header':['NEQ_DecodeScalar.header_result_state_effects'],'m31':['NEQ_DecodeScalar.m31_result_state_effects','NEQ_ParserCanonical.some_canonical'],'digest':['NEQ_DecodeScalar.digest_result_state_effects','NEQ_DecodeScalar.digest_word_domain','NEQ_ParserCanonical.some_canonical']}
def body(source,case):
 if case=='m31':
  a=source.index('    pub fn from_le_bytes(bytes: [u8; 4])');z=source.index('\n    }',a)+6
 else:
  name='fn require_header(' if case=='header' else 'pub fn decode_digest_canonical('
  a=source.index(name);z=source.index('\n}',a)+2
 return source[a:z]
def validate(c,expected,ledger,v):
 try:
  q=c['decode_scalar'];case=q['case'];f=FUNCTIONS[case];assert q['function']==f
  assert q['method']=='actual frozen pure caller, complete Result/value and immutable frame; named emitted definition law'
  assert q['domain']=={'header':'every typed216-byte header, arbitrary magic and either kind','m31':'every four raw bytes','digest':'every typed32-byte input; every accepted output limb and all rejections'}[case]
  assert q['pairs']==PAIRS[case] and all(v.native_pair(*p) for p in q['pairs'])
  from NEQ_artifacts import native_support
  attempts=sorted({a for pair in PAIRS[case] for a in pair});assert q['native_support']==native_support(attempts)
  for r in q['native_support']:v.inherited.artifact(r)
  assert [t['name'] for t in q['theorems']]==THEOREMS[case] and all(v.inherited.theorem(t) for t in q['theorems'])
  for r in q['manifests']:v.inherited.artifact(r)
  assert q['inner_hypotheses_remaining']==[] and q['trust_classification']=='P6/D188 option A reclassification'
  assert q['empty_external_modifies'] and q['ordered_effects']==[] and q['all_return_variants'] and q['all_typed_inputs']
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+f.split('::')[0]],cwd=v.R,text=True);b=body(source,case)
  assert q['frozen_body']==b and q['frozen_body_sha256']==hashlib.sha256(b.encode()).hexdigest()
  p=(v.E/(attempts[0]+'-NEQ_native_contracts.patch')).read_text();assert 'stub_verified' not in p
  if case=='header':
   assert 'let actual=require_header(&bytes,magic,kind)' in p and 'let bytes:[u8;216]=kani::any()' in p
   assert 'b[0]!=m[0]||b[1]!=m[1]||b[2]!=m[2]||b[3]!=m[3]' in p
   assert 'actual==expected' in p
   for text in ['WrongMagic','WrongVersion','WrongTransitionKind','WrongDigestEncoding','NonZeroReserved']:assert text in p
  elif case=='m31':
   assert 'let bytes:[u8;4]=kani::any();let word=u32::from_le_bytes(bytes);let actual=M31::from_le_bytes(bytes).map(|x|x.0)' in p
   assert 'if word >= 2147483647{None}else{Some(word )}' in p and 'actual==expected' in p
   assert 'let v = u32::from_le_bytes(bytes);' in b and 'if v >= P' in b and 'Some(M31(v))' in b
  else:
   assert 'let actual=decode_digest_canonical(&bytes)' in p and 'let bytes:[u8;32]=kani::any()' in p and 'kani::assume(j<8)' in p
   for i in range(8):
    inp=','.join(f'bytes[{4*i+j}]' for j in range(4));assert 'u32::from_le_bytes(['+inp+'])' in p
    assert 'M31::from_le_bytes(['+', '.join(f'bytes[{4*i+j}]' for j in range(4))+'])' in b
    assert f'w[{i}]>=2147483647' in p
   assert 'assert!(d[j].0==w[j]' in p and 'same complete Result variant' in p
   assert b.count('.ok_or(AtomicStatementError::NonCanonicalDigest)?')==8
   assert q['same_child_input']=='every i<8 passes original bytes[4*i..4*i+4] as a typed4 array'
  rs=[r for r in ledger['rows'] if r['function']==f];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={f}|{f+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{f+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
