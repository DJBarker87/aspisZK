"""All-input checked constructor and complete physical opening; no contracts."""
from NEO_native_review import *
FROZEN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def audit():
 out={}
 for name,pos,neg,flag,target in [('index','NEO_K067','NEO_K068','NEO_wrong_index','verifier::NEO_geometry::index_new'),('opening','NEO_K071','NEO_K072','NEO_wrong_opening','verifier::candidate::NEO_opening::opening')]:
  records=[]
  for a,expected in [(pos,0),(neg,1),('NEO_K069',0),('NEO_K070',1)]:
   rc=obj(E/a/'receipt.json');src=snapshot(a);records.append(rc)
   assert rc['exit_status']==expected and rc['limits']==CAPS and rc['swaps']=='0'
   assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and rc['copy_patch_sha256']==KMX
   ad=obj(E/(a+'-admission.json'));assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
   graph=obj(E/(a+'-graph-check.json'));assert graph['exact_frozen_selected_graph']
   assert graph['resolved_features_all_crates']==obj(E/(pos+'-graph-check.json'))['resolved_features_all_crates']
   lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']==LOCK
   assert not obj(E/(a+'-source-check.json'))['errors']
   log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log
   assert 'timed out' not in log.lower()
   for path in ['crates/aspis-core/src/r0/domain.rs','crates/aspis-core/src/r0/mod.rs']:
    assert src['NEO_src/'+path]==subprocess.check_output(['git','show',FROZEN+':'+path],cwd=R,text=True)
   code=src['NEO_src/crates/aspis-r1-cost-probe/src/verifier/NEO_geometry.rs']
   assert not any(x in code for x in ['static mut','Option<fn','stub_verified','proof_for_contract'])
  assert records[0]['source_hashes']==records[1]['source_hashes']
  for rc in records:
   env=dict(rc['env']);env['RUSTFLAGS']=env['RUSTFLAGS'].replace(' --cfg '+flag,'');assert env==records[0]['env']
  assert records[0]['target']==records[1]['target']==target
  for a in [pos,neg]:
   src=snapshot(a)
   path='crates/aspis-r1-cost-probe/src/verifier.rs';frozen=subprocess.check_output(['git','show',FROZEN+':'+path],cwd=R,text=True)
   assert src['NEO_src/'+path]==frozen+'\n#[cfg(kani)]\nmod NEO_geometry;\n'
   if name=='opening':
    path='crates/aspis-r1-cost-probe/src/candidate.rs';frozen=subprocess.check_output(['git','show',FROZEN+':'+path],cwd=R,text=True)
    assert src['NEO_src/'+path]==frozen+'\n#[cfg(kani)]\nmod NEO_opening { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/NEO_opening.rs")); }\n'
    code=src['NEO_src/crates/aspis-r1-cost-probe/src/NEO_opening.rs']
    assert 'let proof:[u8;57607]=kani::any()' in code and 'kani::assume(i<22)' in code
    assert 'core::ptr::eq(actual.as_ptr(),expected.as_ptr())' in code and 'actual.len()==832' in code
   else:
    assert 'let i:usize=kani::any();let actual=FibreIndex::new(i);let expected=NEO_tail::checked(i)' in code
    assert 'Err(aspis_core::r0::Error::IndexOutOfRange)=>expected==Err(0),Err(_)=>false' in code
  pins=obj(E/'NEO_TAIL_EXTRACTION_PINS.json');assert pins['exit']==0
  assert pins['rust_reference_sha256']==sha((E/'NEO_tail_reference.rs').read_bytes())==records[0]['source_hashes']['NEO_src/crates/aspis-r1-cost-probe/src/NEO_tail_reference.rs']
  assert pins['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' and pins['aeneas_sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
  for f,h in pins['outputs'].items():assert sha((E/f).read_bytes())==h==sha((E/'NEO_TailRef'/Path(f).name).read_bytes())
  out[name]=dict(positive=pos,negative=neg,controls=['NEO_K069','NEO_K070'],extraction='NEO_E010',contracts=[],historical_credit_restored=[],k2_quarantined=False,k3_status='UNAFFECTED')
 return out
if __name__=='__main__':
 out=audit();(E/'NEO_TAIL_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n')
