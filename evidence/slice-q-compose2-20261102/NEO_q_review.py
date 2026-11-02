"""Full private-Q pairs: original names, exact KMX, raw carriers, no statics."""
from NEO_native_review import *

def review():
 out={}
 for name,pos,neg in [('q_limbs',24,25),('q_from_limbs',26,27),('q_from_wide',29,30),('limbs_of',31,32),('checked_q',33,34)]:
  rs=[]
  for n,expected in [(pos,0),(neg,1)]:
   a=f'NEO_K{n:03}';rc=obj(E/a/'receipt.json');src=snapshot(a);rs.append(rc)
   assert rc['exit_status']==expected and rc['limits']==CAPS and rc['swaps']=='0'
   assert rc['copy_patch_sha256']==KMX and rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
   assert rc['target']=='fast_pairing::canonical::NEO_q::'+name
   log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log
   assert 'timed out' not in log.lower() and (not expected or '** 1 of ' in log)
   ad=obj(E/(a+'-admission.json'));assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
   graph=obj(E/(a+'-graph-check.json'));assert graph['exact_frozen_selected_graph']
   assert graph['resolved_features_all_crates']==obj(E/'NEO_K020-graph-check.json')['resolved_features_all_crates']
   lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']==LOCK
   assert not obj(E/(a+'-source-check.json'))['errors']
   code=src['NEO_src/crates/aspis-r1-cost-probe/src/NEO_q.rs']
   assert not re.search(r'\bstatic\b|Option\s*<\s*fn|stub_verified|proof_for_contract',code)
   assert '#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]' in code
   assert sha(src['NEO_src/crates/aspis-r1-cost-probe/src/NEO_q_reference.rs'].encode())==sha((E/'NEO_q_reference.rs').read_bytes())
  assert rs[0]['source_hashes']==rs[1]['source_hashes']
  env=dict(rs[1]['env']);env['RUSTFLAGS']=env['RUSTFLAGS'].replace(' --cfg NEO_wrong_q','');assert env==rs[0]['env']
  ex=obj(E/'NEO_Q_EXTRACTION_PINS.json');assert ex['exit']==0
  assert ex['rust_reference_sha256']==sha((E/'NEO_q_reference.rs').read_bytes())
  assert ex['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' and ex['aeneas_sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
  for path,pin in ex['outputs'].items():
   assert sha((E/path).read_bytes())==pin==sha((E/'NEO_QRef'/Path(path).name).read_bytes())
  # Same configuration copy positive and intentionally false assertion.
  for a,expected in [('NEO_K020',0),('NEO_K021',1)]:
   c=obj(E/a/'receipt.json');snapshot(a)
   assert c['exit_status']==expected and c['copy_patch_sha256']==KMX and c['limits']==CAPS
   assert c['env']==rs[0]['env']
   assert ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in (E/a/'stdout.log').read_text()
  out[name]=dict(positive=f'NEO_K{pos:03}',negative=f'NEO_K{neg:03}',full_raw_domain=True,copy_controls=['NEO_K020','NEO_K021'],extraction='NEO_E004',k2_quarantined=False,k3_status='UNAFFECTED',historical_credit_restored=[],contracts=[])
 return out
if __name__=='__main__':
 d=review();(E/'NEO_Q_REVIEW.json').write_text(json.dumps(d,indent=1)+'\n');print(json.dumps(d))
