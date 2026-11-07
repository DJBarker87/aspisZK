from NMM_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
COMMON='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn NMM_digest_reference(bytes: &[u8;32]) -> Result<[M31;8],aspis_statement::AtomicStatementError> {
 let mut out=[M31::ZERO;8];
 for i in 0..8 {
  let w=u32::from_le_bytes([bytes[4*i],bytes[4*i+1],bytes[4*i+2],bytes[4*i+3]]);
  if w>=2147483647 {return Err(aspis_statement::AtomicStatementError::NonCanonicalDigest);}
  out[i]=M31(w);
 }
 Ok(out)
}
fn NMM_digest_cut(bytes: &[u8;32]) -> Result<[M31;8],aspis_statement::AtomicStatementError> {
 // TX2:146: every32-byte array; no canonical-input precondition. All returned
 // words are havocked, then constrained to the CLOSED complete decoder law.
 assert!(bytes.len()==32,"TX2:146 own argument domain");
 let expected=NMM_digest_reference(bytes);
 match expected {
  Err(e)=>Err(e),
  Ok(value)=>{
   let raw:[u32;8]=kani::any();
   for i in 0..8 {kani::assume(raw[i]==value[i].0);}
   Ok(raw.map(M31))
  }
 }
}
fn NMM_same(a:&Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>,b:&Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>)->bool {
 match (a,b) {
  (Err(x),Err(y))=>x==y,
  (Ok(x),Ok(y))=>x.bump==y.bump&&x.master==y.master&&x.lane_id==y.lane_id&&x.tree.next_leaf_index==y.tree.next_leaf_index&&x.tree.root==y.tree.root&&x.tree.frontier==y.tree.frontier,
  _=>false
 }
}
'''
ANN='''#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(aspis_statement::atomic_statement::decode_digest_canonical,NMM_digest_cut)]
'''
def attempt(a,branch,mode):
 frozen=(E/'NMM_FROZEN_217.rs').read_text()
 ref=frozen.replace('fn decode_lane_from_pool_release(', 'fn NMM_lane_reference(',1).replace('decode_digest_canonical(', 'NMM_digest_reference(')
 # Original full extent, every content byte arbitrary. Branch restrictions are
 # predicates on this input only; no child outcome is supplied as a premise.
 domains={'whole':'true','header':'bytes[..4]!=POOL_V1_PAIR_FOREST_LANE_MAGIC','prefix':'bytes[..4]==POOL_V1_PAIR_FOREST_LANE_MAGIC && bytes[4]==POOL_V1_PAIR_FOREST_LANE_VERSION && bytes[5]<POOL_V1_PAIR_FOREST_LANE_COUNT as u8 && bytes[6]==POOL_V1_PAIR_FOREST_LANE_COUNT as u8 && bytes[7]==POOL_V1_PAIR_TREE_DEPTH as u8 && bytes[8..40]==POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING && bytes[73..80].iter().all(|x|*x==0)'}
 text=COMMON+ref+ANN+'''fn stage(){
 let bytes:[u8;768]=kani::any();
 kani::assume(DOMAIN);
 let observer:usize=kani::any();kani::assume(observer<768);
 let before=bytes[observer];
 let native=decode_lane_from_pool_release(&bytes);
 let reference=NMM_lane_reference(&bytes);
 assert!(NMM_same(&native,&reference)&&bytes[observer]==before,"complete returned Result and lane fields; immutable input frame");
}
'''.replace('DOMAIN',domains[branch])
 if mode=='spec':text=text.replace('raw[i]==value[i].0','raw[i]==(value[i].0^1)')
 if mode=='argument':text=text.replace('decode_lane_from_pool_release(&bytes)','decode_lane_from_pool_release(&bytes[1..])')
 if mode=='footprint':text=text.replace('raw[i]==value[i].0','i==7 || raw[i]==value[i].0')
 if mode=='copy':text=text.replace('assert!(NMM_same(&native,&reference)&&bytes[observer]==before,','let mut copy=[0u8;768];copy.copy_from_slice(&bytes);assert!(copy[observer]!=(bytes[observer]),')
 module='NMM_lane'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+module+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(row='TX2:217',branch=branch,mode=mode,complete_native_function=True,original_length=768,arbitrary_contents=True,stub='NMM_digest_cut',callee='TX2:146',domain='Every &[u8;32]',footprint='Full returned eight-word digest or exact NonCanonicalDigest error; immutable input; no owned child allocation',native_limits='Does not yet observe full allocator state/abort and cleanup; no candidate root from value-only result'),indent=2)+'\n')
 return submit(a,'r1_pool_adapter::'+module+'::stage',P,module,text,mode)
if __name__=='__main__':
 import sys
 rc=attempt(*sys.argv[1:]);sys.exit(rc['exit_status'])
