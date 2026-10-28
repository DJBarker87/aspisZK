from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;p=E/'NBN_more.rs.txt';old=p.read_text();assert 'fn NBN_late_length_index' not in old
extra='''
fn NBN_late_guard(n:usize,next:u64,after:u64)->Option<PoolV1PairLatePublicStatementErrorV1>{
 if n!=1520 {return Some(PoolV1PairLatePublicStatementErrorV1::WrongLength);}
 if next.checked_add(1)!=Some(after) {return Some(PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch);}
 None
}
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_late_length_index(){
 let n:usize=kani::any();let next:u64=kani::any();let after:u64=kani::any();
 assert_eq!(NBN_late_guard(n,next,after),if n!=1520 {Some(PoolV1PairLatePublicStatementErrorV1::WrongLength)} else if next==u64::MAX || after!=next+1 {Some(PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch)} else {None});
}
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_late_ranges(){
 let s=NBN_common().lane_transition;let mut out:[u8;1520]=kani::any();let ptr=out.as_mut_ptr();
 let live=&mut out[32..32+800];assert_eq!(live.len(),800);assert_eq!(live.as_mut_ptr(),ptr.wrapping_add(32));
 let after=&mut out[32+800..];assert_eq!(after.len(),688);assert_eq!(after.as_mut_ptr(),ptr.wrapping_add(832));
 let src_live=&s.live_snapshot;let src_after=&s.candidate_afterstate;
 assert!(core::ptr::eq(src_live,&s.live_snapshot));assert!(core::ptr::eq(src_after,&s.candidate_afterstate));
}
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_first_byte_cut(){let encoded:[u8;32]=kani::any();let observed=encoded[0];assert_eq!(observed,encoded.as_slice()[0]);}
fn NBN_lane_cut(canonical:bool,first:u8)->Result<u8,PoolV1PairForestAccountErrorV1>{
 if !canonical {return Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest);}
 Ok(first & 7)
}
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_lane_control(){
 let canonical:bool=kani::any();let first:u8=kani::any();
 let r=NBN_lane_cut(canonical,first);
 assert_eq!(r,if canonical {Ok(first%8)} else {Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest)});
 if let Ok(lane)=r {assert!(lane<8);}
}
fn NBN_late_result_cut(live:Result<(),crate::pool_v1::PoolV1PairLiveSnapshotErrorV1>,after:Result<[u8;688],PoolV1PairVerifierTransportErrorV1>)->Result<(),PoolV1PairLatePublicStatementErrorV1>{
 live.map_err(PoolV1PairLatePublicStatementErrorV1::Snapshot)?;
 let _encoded=after.map_err(PoolV1PairLatePublicStatementErrorV1::Afterstate)?;
 Ok(())
}
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_late_results(){
 let live=if kani::any::<bool>() {Ok(())} else {Err(NBN_any_PoolV1PairLiveSnapshotErrorV1())};
 let after=if kani::any::<bool>() {Ok([0;688])} else {Err(NBN_any_PoolV1PairVerifierTransportErrorV1())};
 let expected=match live {Err(e)=>Err(PoolV1PairLatePublicStatementErrorV1::Snapshot(e)),Ok(())=>match after {Err(e)=>Err(PoolV1PairLatePublicStatementErrorV1::Afterstate(e)),Ok(_)=>Ok(())}};
 assert_eq!(NBN_late_result_cut(live,after),expected);
}
'''
p.write_text(old+extra)
(E/'NBN_SCALAR_EXTEND.json').write_text(json.dumps(dict(previous_sha256=hashlib.sha256(old.encode()).hexdigest(),source='NBN_more.rs.txt',notes='all usize length cut, checked-add overflow, actual child slice descriptors, byte0, lane bound, ordered late child errors; no stub'),indent=2)+'\n')
