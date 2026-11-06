from NKF_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
COMMON='''use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn digest()->[M31;8]{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
fn frontier()->[[M31;8];20]{let raw:[[u32;8];20]=kani::any();raw.map(|r|r.map(|x|M31(x)))}
'''
def iteration():
 return COMMON+'''
struct Log{count:u8,pointer:usize,length:usize,input:u8}
fn oracle(bytes:&[u8;32],canonical:bool,words:[M31;8],log:&mut Log,i:usize)->Result<[M31;8],aspis_statement::AtomicStatementError>{log.count+=1;log.pointer=bytes.as_ptr() as usize;log.length=bytes.len();log.input=bytes[i];if canonical{Ok(words)}else{Err(aspis_statement::AtomicStatementError::NonCanonicalDigest)}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn iteration(){
 let tree:[u8;688]=kani::any();let level:usize=kani::any();let other:usize=kani::any();let word:usize=kani::any();let i:usize=kani::any();kani::assume(level<20&&other<20&&word<8&&i<32);
 let next_leaf_index:u64=kani::any();let words=digest();let canonical:bool=kani::any();let mut frontier=frontier();let before=frontier;
 let mut log=Log{count:0,pointer:0,length:0,input:0};
 let result=(||->ProgramResult{
  let node=&mut frontier[level];let start=48+32*level;
  *node=oracle(tree[start..start+32].try_into().map_err(|_|ProgramError::InvalidAccountData)?,canonical,words,&mut log,i).map_err(|_|ProgramError::InvalidAccountData)?;
  if (next_leaf_index>>level)&1==0&&*node!=v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[level]{return Err(ProgramError::InvalidAccountData);}
  Ok(())
 })();
 let expected_ok=canonical&&((next_leaf_index>>level)&1!=0||words==v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[level]);
 let expected=if canonical&&other==level{words[word].0}else{before[other][word].0};
 let tag=if expected_ok{matches!(result,Ok(()))}else{matches!(result,Err(ProgramError::InvalidAccountData))};
 let good=tag&&frontier[other][word].0==expected&&log.count==1&&log.length==32&&log.pointer==tree[48+32*level..].as_ptr() as usize&&log.input==tree[48+32*level+i];
 assert!(if cfg!(NKF_invert){!good}else{good},"lane iteration Result write-before-reject window and frame");
}
'''
def constructor():
 return COMMON+'''
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn constructor(){
 let bytes:[u8;768]=kani::any();let master:[u8;32]=kani::any();let next_leaf_index:u64=kani::any();let root=digest();let frontier=frontier();
 let i:usize=kani::any();let level:usize=kani::any();let word:usize=kani::any();kani::assume(i<32&&level<20&&word<8);
 let out=Box::new(PoolV1PairForestLaneStateV1{bump:bytes[72],master,lane_id:bytes[5],tree:IncrementalMerkleTreeV1{next_leaf_index,root,frontier}});
 let good=out.bump==bytes[72]&&out.master[i]==master[i]&&out.lane_id==bytes[5]&&out.tree.next_leaf_index==next_leaf_index&&out.tree.root[word].0==root[word].0&&out.tree.frontier[level][word].0==frontier[level][word].0;
 assert!(if cfg!(NKF_invert){!good}else{good},"lane full constructor scalar window");
}
'''
if __name__=='__main__':
 import sys
 a,part,mode=sys.argv[1:];text=globals()[part]();submit(a,'r1_pool_adapter::NKF_lane::'+part,P,'NKF_lane',text,mode)
