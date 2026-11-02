"""Complete live/after encoder certificates, only split native windows/steps."""
import json,hashlib,subprocess
P='crates/aspis-statement/src/pool_v1/'
CASES={
 'live':dict(function=P+'pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1',windows=[[0,8],[8,1],[16,32],[48,32],[80,32],[112,8],[120,8],[128,32]],pairs=[[f'NEM_K{i:03}',f'NEM_K{i+1:03}'] for i in range(39,55,2)]+[['NEM_K053','NEM_K070'],['NEM_K035','NEM_K036'],['NEM_K072','NEM_K073'],['NEM_K076','NEM_K077'],['NEM_K078','NEM_K079']],base=160,length=800),
 'after':dict(function=P+'pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1',windows=[[0,4],[4,1],[5,1],[6,1],[7,1],[8,8],[16,32]],pairs=[['NEM_K055','NEM_K056'],['NEM_K057','NEM_K058']]+[[f'NEM_K{i:03}',f'NEM_K{i+1:03}'] for i in range(60,70,2)]+[['NEM_K068','NEM_K071'],['NEM_K074','NEM_K075'],['NEM_K076','NEM_K077'],['NEM_K080','NEM_K081'],['NEM_K082','NEM_K083']],base=48,length=688)}
ALTERNATIVES=['crates/aspis-core/src/field.rs::M31::to_le_bytes','crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes']

def validate(c,expected,ledger,v):
 try:
  q=c['encoder_composition'];case=q['case'];spec=CASES[case];f=spec['function']
  assert q['function']==f and q['method']=='native prefix, each framed header/root window, separated iterator/geometry/byte step, accepted induction'
  assert q['all_typed_inputs'] and q['all_slice_lengths'] and q['full_Result_state_effects']
  assert q['trust_classification']=='P6/D188 option A reclassification'
  assert q['windows']==spec['windows'] and q['native_pairs']==spec['pairs']
  assert q['frontier']==dict(base=spec['base'],count=20,width=32,destination_length=spec['length'])
  assert q['empty_child_modifies'] and q['no_new_copy_stub'] and q['inner_hypotheses_remaining']==[]
  assert q['canonical_domain']=='composed raw digest encoder is total; validator-derived canonical domain also follows from NBN_ValidatorDomains'
  assert q['legacy_decode_qualification']=='direct emitted encoder proof has no decode premise or reached native decode call; no decoder row is promoted'
  assert all(v.native_pair(*p) for p in spec['pairs'])
  L=v.R/'evidence/slice-s-compose4-20261101';assert v.native_pair('NEL_K058','NEL_K059',folder=L,prefix='NEL_')
  from NEM_artifacts import native_support,ref
  required=native_support(list(dict.fromkeys(a for pair in spec['pairs'] for a in pair)))
  required += [ref(L/n) for a in ['NEL_K058','NEL_K059'] for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEL_native_contracts.patch',a+'-NEL_oracle.patch']]
  assert q['native_support']==required
  for r in q['native_support']:v.inherited.artifact(r)
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+f.split('::')[0]],cwd=v.R,text=True)
  a=source.index('pub fn '+f.split('::')[1]+'(');z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  assert f'let start = {spec["base"]} + 32 * level;' in body
  field='frontier' if case=='live' else 'next_frontier';receiver='snapshot' if case=='live' else 'afterstate'
  assert f'{receiver}.{field}.iter().enumerate()' in body
  assert 'output[start..start + 32].copy_from_slice(&encode_digest_canonical(node));' in body
  assert body.count('for (level, node)')==1 and body.count('encode_digest_canonical')==2
  assert 'decode_' not in body
  wanted=['NEM_EncoderFrame.'+case+'_value_and_frame','NEM_EncoderFrame.'+case+'_step_and_bytes','NEM_EncoderFrame.frontier_next']
  if case=='live':wanted+=['NEM_EncoderFrame.fill_value']
  assert [t['name'] for t in q['theorems']]==wanted and all(v.inherited.theorem(t) for t in q['theorems'])
  if case=='live':
   assert 'output.fill(0);' in body
   std=json.loads(v.inherited.artifact(q['std_fill_pin']))
   assert std['toolchain']=='nightly-2025-11-21-x86_64-unknown-linux-gnu'
   assert 'crate::intrinsics::write_bytes(self.as_mut_ptr(), value, self.len());' in std['snippet']
   assert 'for item' not in std['snippet'] and 'for el' not in std['snippet'] and 'while ' not in std['snippet']
  else:assert 'let mut output = [0u8; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES];' in body
  rs=[r for r in ledger['rows'] if r['function']==f];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={f}|{f+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{f+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  if c['kind']=='alternative-resolution':
   assert expected in {f+' -> '+x for x in ALTERNATIVES}
   assert 'pub next_pair_index: u64,' in source and f'{receiver}.next_pair_index.to_le_bytes()' in body
   if case=='live':assert 'pub sequence: u64,' in source and 'snapshot.sequence.to_le_bytes()' in body
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
