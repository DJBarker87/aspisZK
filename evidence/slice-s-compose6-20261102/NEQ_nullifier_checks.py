import subprocess,hashlib
BASE='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::'
FUNCTIONS={case:BASE+'PoolV1PairForestTerminal'+('Statement' if case=='statement' else 'Payment')+'V1::nullifier' for case in ['statement','payment']}
THEOREMS=['NEQ_NullifierDomains.statement_result_frame','NEQ_NullifierDomains.payment_result_frame','NEQ_NullifierDomains.common_independent']
def validate(c,expected,ledger,v):
 try:
  q=c['nullifier_getter'];case=q['case'];f=FUNCTIONS[case];assert q['function']==f
  pair=['NEQ_K083','NEQ_K084'] if case=='statement' else ['NEQ_K085','NEQ_K086']
  assert q['pairs']==[pair] and v.native_pair(*pair)
  assert q['method']=='ruling y prime exact borrowed-place identity and same-variant extracted projection'
  assert q['domain']=='every typed variant and raw Digest; no validation or canonicality assumption'
  assert q['inner_hypotheses_remaining']==[] and q['trust_classification']=='P6/D188 option A reclassification'
  from NEQ_artifacts import native_support
  assert q['native_support']==native_support(pair)
  for r in q['native_support']:v.inherited.artifact(r)
  assert [t['name'] for t in q['theorems']]==THEOREMS and all(v.inherited.theorem(t) for t in q['theorems'])
  for r in q['manifests']:v.inherited.artifact(r)
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+f.split('::')[0]],cwd=v.R,text=True)
  impl=f.split('::')[1];a=source.index('impl '+impl+' {');a=source.index('    pub fn nullifier(',a);z=source.index('\n    }',a)+6;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  suffix='{ public, .. }' if case=='statement' else '(public)'
  pattern='''    pub fn nullifier(&self) -> &Digest {
        match self {
            Self::PrivateTransferSUFFIX => &public.nullifier,
            Self::WithdrawalSUFFIX => &public.nullifier,
        }
    }'''.replace('SUFFIX',' '+suffix if case=='statement' else suffix)
  assert body==pattern
  pos=(v.E/(pair[0]+'-NEQ_native_contracts.patch')).read_text();neg=(v.E/(pair[1]+'-NEQ_native_contracts.patch')).read_text()
  assert 'let actual=s.nullifier()' in pos and 'core::ptr::eq(actual,expected)' in pos
  assert '=>&public.nullifier' in pos and '=>&public.anchor_root' in neg
  assert q['empty_external_modifies'] and q['ordered_effects']==[] and q['same_borrowed_place']
  rs=[r for r in ledger['rows'] if r['function']==f]
  allowed={f}|{f+'::'+h['name'] for r in rs for h in r['named_hypotheses']}
  assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
