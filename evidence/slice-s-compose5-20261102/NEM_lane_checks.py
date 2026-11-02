"""Import NEL's controlled native first-byte/lane caller without reproof."""
import json,hashlib,subprocess
P='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::'

def validate(c,expected,ledger,v):
 try:
  q=c['lane_composition'];case=q['case'];assert case in ['first','lane'];f=P+('first_canonical_byte' if case=='first' else 'pool_v1_pair_forest_output_lane_v1')
  assert q['function']==f and q['method']=='reused NEL total native Result/order and exact immutable argument frames'
  assert q['all_raw_digests'] and q['empty_external_modifies'] and q['full_Result']
  assert q['trust_classification']=='P6/D188 option A reclassification'
  pairs=[['NEL_K030','NEL_K031'],['NEL_K058','NEL_K059']] if case=='first' else [['NEL_K002','NEL_K003'],['NEL_K058','NEL_K059']]
  assert q['native_pairs']==pairs
  L=v.R/'evidence/slice-s-compose4-20261101';assert all(v.native_pair(*p,folder=L,prefix='NEL_') for p in pairs)
  from NEM_artifacts import ref
  required=[ref(L/n) for pair in pairs for a in pair for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEL_native_contracts.patch',a+'-NEL_oracle.patch']]
  assert q['native_support']==required
  for r in required:v.inherited.artifact(r)
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+f.split('::')[0]],cwd=v.R,text=True)
  header=('fn first_canonical_byte(' if case=='first' else 'pub fn pool_v1_pair_forest_output_lane_v1(')
  a=source.index(header);z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  if case=='first':
   assert body=='fn first_canonical_byte(digest: &Digest) -> u8 {\n    encode_digest_canonical(digest)[0]\n}'
   assert q['child_log']=='encode(same raw digest), return reply[0]'
   wanted=['NED_SubtreeComposition.first_byte','NED_DigestCohorts.first_byte']
  else:
   assert 'if !digest_is_canonical(nullifier)' in body and 'Ok(first_canonical_byte(nullifier) & 7)' in body
   assert q['child_log']=='canonical(same nullifier); if true first(same nullifier); no later call on error'
   wanted=['NEM_LaneReached.lane_instance','NEM_LaneReached.lane_reached']
  assert [t['name'] for t in q['theorems']]==wanted and all(v.inherited.theorem(t) for t in q['theorems'])
  rs=[r for r in ledger['rows'] if r['function']==f];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={f}|{f+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{f+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
