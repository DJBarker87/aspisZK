import subprocess,hashlib
F='crates/aspis-statement/src/atomic_statement.rs::unwrap_fixed_slice'
PAIRS=[['NEQ_K096','NEQ_K097'],['NEQ_K098','NEQ_K099'],['NEQ_K100','NEQ_K101'],['NEQ_K106','NEQ_K107']]
THEOREMS=['NEQ_UnwrapDomains.ok_result_state_effects','NEQ_UnwrapDomains.err_result_state_effects','NEQ_UnwrapDomains.fixed_read_packet']
def validate(c,expected,ledger,v):
 try:
  q=c['unwrap_conversion'];assert q['function']==F and q['pairs']==PAIRS
  assert q['method']=='uniform generic Copy match; actual fixed-byte owned and borrowed caller instances; derived Ok conversions'
  assert q['domain']=='generic Copy success payload; actual callers derive fixed-width Ok; Err panic model retained, no new native Err credit'
  assert q['inner_hypotheses_remaining']==[] and q['trust_classification']=='P6/D188 option A reclassification'
  assert all(v.native_pair(*p) for p in PAIRS)
  from NEQ_artifacts import native_support
  attempts=sorted({a for pair in PAIRS for a in pair});assert q['native_support']==native_support(attempts)
  for r in q['native_support']:v.inherited.artifact(r)
  assert [t['name'] for t in q['theorems']]==THEOREMS and all(v.inherited.theorem(t) for t in q['theorems'])
  for r in q['manifests']:v.inherited.artifact(r)
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+F.split('::')[0]],cwd=v.R,text=True);a=source.index('pub(crate) fn unwrap_fixed_slice');z=source.index('\n}',a)+2;b=source[a:z]
  assert q['frozen_body']==b and q['frozen_body_sha256']==hashlib.sha256(b.encode()).hexdigest()
  assert b=='''pub(crate) fn unwrap_fixed_slice<T: Copy>(value: Result<T, core::array::TryFromSliceError>) -> T {
    match value {
        Ok(value) => value,
        Err(_) => panic!("fixed-size slice conversion failed"),
    }
}'''
  for (pos,neg),width in zip(PAIRS[:3],[4,8,32]):
   p=(v.E/(pos+'-NEQ_native_contracts.patch')).read_text();assert f'let input:[u8;{width}]' in p and 'let actual=unwrap_fixed_slice(Ok(input))' in p and 'actual[j]==original' in p
  p=(v.E/'NEQ_K106-NEQ_native_contracts.patch').read_text();assert 'let actual=unwrap_fixed_slice(Ok(&input))' in p and 'core::ptr::eq(actual,&input)' in p
  assert q['empty_external_modifies'] and q['same_owned_or_borrowed_carrier'] and q['ordered_effects']==[]
  rs=[r for r in ledger['rows'] if r['function']==F];allowed={F}|{F+'::'+h['name'] for r in rs for h in r['named_hypotheses']};assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
