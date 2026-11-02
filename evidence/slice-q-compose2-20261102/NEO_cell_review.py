"""New indexed getter bodies, independent reference and same-source copy controls."""
from NEO_native_review import *
def audit():
 out={}
 for name,pos,neg,body in [('basis_cell','NEO_K047','NEO_K048','fn basis_at(basis:&[M31;256],index:usize)->M31 {basis[index]}'),('accumulated_cell','NEO_K049','NEO_K050','fn accumulated_weight_at(weights:&[K],index:usize)->K {weights[index]}')]:
  records=[]
  for a,expected in [(pos,0),(neg,1),('NEO_K051',0),('NEO_K052',1)]:
   rc=obj(E/a/'receipt.json');src=snapshot(a);records.append(rc)
   assert rc['exit_status']==expected and rc['limits']==CAPS and rc['swaps']=='0'
   assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and rc['copy_patch_sha256']==KMX
   ad=obj(E/(a+'-admission.json'));assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
   graph=obj(E/(a+'-graph-check.json'));assert graph['exact_frozen_selected_graph']
   assert graph['resolved_features_all_crates']==obj(E/(pos+'-graph-check.json'))['resolved_features_all_crates']
   lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']==LOCK
   assert not obj(E/(a+'-source-check.json'))['errors']
   log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log
   assert 'timed out' not in log.lower() and (not expected or '** 1 of ' in log)
   code=src['NEO_src/crates/aspis-r1-cost-probe/src/verifier/NEO_geometry.rs'];assert not any(x in code for x in ['static mut','Option<fn','stub_verified','proof_for_contract'])
   assert 'NEO_cell_reference::cell' in code and '#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]' in code
   frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R,text=True)
   assert src['NEO_src/crates/aspis-r1-cost-probe/src/verifier.rs']==frozen+'\n#[cfg(kani)]\nmod NEO_geometry;\n' and body in frozen
  for rc in records[1:]:assert rc['source_hashes']==records[0]['source_hashes']
  for rc in records:
   env=dict(rc['env']);env['RUSTFLAGS']=env['RUSTFLAGS'].replace(' --cfg NEO_wrong_cell','');assert env==records[0]['env']
  for rc in records[:2]:assert rc['target']=='verifier::NEO_geometry::'+name
  pins=obj(E/'NEO_CELL_EXTRACTION_PINS.json');assert pins['exit']==0
  assert pins['rust_reference_sha256']==sha((E/'NEO_cell_reference.rs').read_bytes())==records[0]['source_hashes']['NEO_src/crates/aspis-r1-cost-probe/src/NEO_cell_reference.rs']
  assert pins['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' and pins['aeneas_sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
  for f,h in pins['outputs'].items():assert sha((E/f).read_bytes())==h==sha((E/'NEO_CellRef'/Path(f).name).read_bytes())
  out[name]=dict(positive=pos,negative=neg,controls=['NEO_K051','NEO_K052'],extraction='NEO_E007',contracts=[],historical_credit_restored=[],k2_quarantined=False,k3_status='UNAFFECTED')
 return out
if __name__=='__main__':
 out=audit();(E/'NEO_CELL_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n')
