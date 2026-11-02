"""Total live/after validators by exact prefix and one native loop step."""
import json,hashlib,subprocess
CASES={
 'live':dict(function='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1',prefix=['NEM_K030','NEM_K031'],step=['NEM_K026','NEM_K027'],frontier='frontier'),
 'after':dict(function='crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate',prefix=['NEM_K033','NEM_K034'],step=['NEM_K028','NEM_K029'],frontier='next_frontier')}

def validate(c,expected,ledger,v):
 try:
  q=c['frontier_validator'];case=q['case'];spec=CASES[case];f=spec['function']
  assert q['function']==f and q['method']=='native scalar prefix plus arbitrary frontier step; accepted NBH induction'
  assert q['all_typed_inputs'] and q['all_raw_frontiers'] and q['empty_external_modifies']
  assert q['prefix']==spec['prefix'] and q['step']==spec['step']
  assert q['invariant']=='0<=level<=20; original frontier; exact external frame; next scanner argument=frontier[level]'
  assert q['ordered_children']=='root first, then increasing frontier indices until first rejection'
  assert q['trust_classification']=='P6/D188 option A reclassification'
  assert v.native_pair(*spec['prefix']) and v.native_pair(*spec['step'])
  from NEM_artifacts import native_support
  assert q['native_support']==native_support(spec['prefix']+spec['step'])
  for r in q['native_support']:v.inherited.artifact(r)
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+f.split('::')[0]],cwd=v.R,text=True)
  a=source.index('fn '+f.split('::')[1]+'(');z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  loop=body[body.index('    let mut level = 0;'):body.rindex('    Ok(())')]
  assert q['loop_source']==loop
  variable='snapshot' if case=='live' else 'afterstate'
  assert 'while level < '+variable+'.'+spec['frontier']+'.len()' in loop
  assert '&'+variable+'.'+spec['frontier']+'[level]' in loop
  assert loop.count('level += 1;')==1
  for a in spec['step']:
   text=(v.E/(a+'-NEM_native_contracts.patch')).read_text()
   assert 'while level<s.'+spec['frontier']+'.len()' in text
   assert 'child(&s.'+spec['frontier']+'[level],f)' in text
   assert 'level+=1;f.end=level;return Ok(());' in text
   assert '#[kani::unwind(2)]' in text and 'kani::assume(start<=20)' in text
   assert 'f.called==(start<20)' in text
  assert [t['name'] for t in q['theorems']]==['NEM_FrontierValidatorInstance.'+case+'_step','NEM_FrontierValidatorInstance.'+case+'_result_and_frame']
  assert all(v.inherited.theorem(t) for t in q['theorems'])
  assert q['induction']=='NBH_FrontierTrace over NBD_DigestTrace.Trace; NBH_LiveValidator.source / NBH_Validators.afterstate'
  rs=[r for r in ledger['rows'] if r['function']==f];obs=[o for r in rs for o in r['caller_domain_obligations']]
  assert all(g=='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical' for r in rs for g in r['canonical_callees'])
  allowed={f}|{f+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{f+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
