use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
type F=PoolV1PairForestAccountErrorV1;
// The real mutable-iterator next is executed once on the arbitrary remaining
// suffix. The entered body is the frozen decoder's single iteration verbatim.
fn iteration(bytes:&[u8;192],lane:usize,lanes:&mut [u64;8])->Option<Result<(),F>>{
 let mut it=lanes[lane..].iter_mut();let sequence=it.next()?;
 let start = CHECKPOINT_LANE_SEQUENCES_OFFSET + 8 * lane;
 *sequence = u64::from_le_bytes(bytes[start..start + 8].try_into().unwrap());
 if *sequence > POOL_V1_PAIR_CAPACITY {
     return Some(Err(PoolV1PairForestAccountErrorV1::InvalidMasterState));
 }
 Some(Ok(()))
}
fn word(b:&[u8],a:usize)->u64{
 (b[a] as u64)|((b[a+1] as u64)<<8)|((b[a+2] as u64)<<16)|((b[a+3] as u64)<<24)|((b[a+4] as u64)<<32)|((b[a+5] as u64)<<40)|((b[a+6] as u64)<<48)|((b[a+7] as u64)<<56)
}
#[kani::proof] #[kani::unwind(12)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn step(){
 let b:[u8;192]=kani::any();let before:[u64;8]=kani::any();
 let j:usize=kani::any();kani::assume(j<8);let original_before=before[j];let frame_i:usize=kani::any();kani::assume(frame_i<192);let original_byte=b[frame_i];
 let lane:usize=kani::any();kani::assume(lane<=8);
 kani::assume(lane<=0||before[0]<=POOL_V1_PAIR_CAPACITY);
 kani::assume(lane<=1||before[1]<=POOL_V1_PAIR_CAPACITY);
 kani::assume(lane<=2||before[2]<=POOL_V1_PAIR_CAPACITY);
 kani::assume(lane<=3||before[3]<=POOL_V1_PAIR_CAPACITY);
 kani::assume(lane<=4||before[4]<=POOL_V1_PAIR_CAPACITY);
 kani::assume(lane<=5||before[5]<=POOL_V1_PAIR_CAPACITY);
 kani::assume(lane<=6||before[6]<=POOL_V1_PAIR_CAPACITY);
 kani::assume(lane<=7||before[7]<=POOL_V1_PAIR_CAPACITY);
 let mut after=before;let r=iteration(&b,lane,&mut after);assert!(before[j]==original_before);assert!(b[frame_i]==original_byte);
 if lane<8{
  let value=word(&b,112+8*lane);
  assert!((after[lane]==value)!=cfg!(NJI_invert));
  assert!(after[j]==if j==lane{value}else{before[j]});
  assert!(r==Some(if value>POOL_V1_PAIR_CAPACITY{Err(F::InvalidMasterState)}else{Ok(())}));
  if r==Some(Ok(()))&&j<=lane{assert!(after[j]<=POOL_V1_PAIR_CAPACITY);}
 }else{assert!(r.is_none());assert!(after[j]==before[j]);}
}
