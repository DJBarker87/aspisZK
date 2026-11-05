from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
p=E/'NHG_public_plan.rs.txt';s=p.read_text();sem=(E/'NHG_semantic.rs.txt').read_text();init=sem[sem.index(' let p=PoolV1'):sem.index(' let result=public.semantic()')]
s+='''
struct TailLog{calls:usize,window:usize,seen:bool,fail:bool,error:Error,row:usize,word:usize,frontier:bool,value:u32,owner:*const alloc::vec::Vec<u8>,place:*const alloc::vec::Vec<u8>,observe:usize,before_len:usize,before_byte:u8,after_len:usize,after_byte:u8}
fn tail_reply(out:&mut alloc::vec::Vec<u8>,log:&mut TailLog,max:usize)->Result<(),Error>{
 let j=log.calls;log.calls+=1;assert_eq!(out as *const _,log.place);
 if j==log.window{log.seen=true;log.owner=out;log.before_len=out.len();log.before_byte=if log.observe<out.len(){out[log.observe]}else{0};
  let length:usize=kani::any();kani::assume(length>=out.len()&&length<=out.len()+max);
  if cfg!(NHG_invert){kani::assume(length>out.len()&&log.observe>=out.len()&&log.observe<length);}
  // Every byte of the capacity was initialized before truncating; u8 has no Drop.
  unsafe{out.set_len(length)}
  log.after_len=length;log.after_byte=if log.observe<length{out[log.observe]}else{0};
  if log.fail{return Err(log.error)}
 }
 Ok(())
}
fn tail_fields(out:&mut alloc::vec::Vec<u8>,s:&[M31],log:&mut TailLog)->Result<(),Error>{if log.calls==log.window{assert_eq!(s.len(),8);log.frontier=false;log.value=s[log.word].0;}tail_reply(out,log,32)}
fn tail_frontier(out:&mut alloc::vec::Vec<u8>,s:&[Digest;20],log:&mut TailLog)->Result<(),Error>{if log.calls==log.window{log.frontier=true;log.value=s[log.row][log.word].0;}tail_reply(out,log,640)}
fn NHG_tail_control(mut out:alloc::vec::Vec<u8>,t:&PoolV1PairLatePublicStatementV1,log:&mut TailLog)->Result<alloc::vec::Vec<u8>,Error>{
 // Borrow fission of the by-value snapshots: K040/K041 plus SnapshotViews
 // identify every used coordinate; CLOSED children are value-extensional.
 let source=&t.live_snapshot;
 let after=&t.candidate_afterstate;
 log.place=&out;
 tail_frontier(&mut out,&source.frontier,log)?;
 tail_fields(&mut out,&after.next_root,log)?;
 tail_frontier(&mut out,&after.next_frontier,log)?;
 Ok(out)
}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_public_tail(){
'''+init+'''
 let n:usize=kani::any();kani::assume(n>=1&&n<=815);let mut out=kani::vec::exact_vec::<u8,1884>();out.truncate(n);let pointer=out.as_ptr();let observe:usize=kani::any();kani::assume(observe<1455);let old=if observe<n{out[observe]}else{0};
 let window:usize=kani::any();kani::assume(window<3);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);let fail:bool=kani::any();let error=any_error();
 let mut log=TailLog{calls:0,window,seen:false,fail,error,row,word,frontier:false,value:0,owner:core::ptr::null(),place:core::ptr::null(),observe,before_len:0,before_byte:0,after_len:0,after_byte:0};
 let got=NHG_tail_control(out,&t,&mut log);assert!(log.seen);assert_eq!(log.calls,if fail{window+1}else{3});assert_eq!(log.owner,log.place);assert_eq!(log.before_len,n);if observe<n{assert_eq!(log.before_byte,old);}
 assert_eq!(log.frontier,window!=1);assert_eq!(log.value,match window{0=>t.live_snapshot.frontier[row][word].0,1=>t.candidate_afterstate.next_root[word].0,_=>t.candidate_afterstate.next_frontier[row][word].0});
 match got{Err(e)=>{assert!(fail);assert_eq!(e,error)},Ok(out)=>{assert!(!fail);assert_eq!(out.as_ptr(),pointer);assert_eq!(out.len(),log.after_len);if observe<out.len(){assert_eq!(out[observe],log.after_byte^if cfg!(NHG_invert){1}else{0});}}}
}
''';p.write_text(s)
m=json.loads((E/'NHG_OVERLAY.json').read_text());(E/'NHG_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256((E/v).read_bytes()).hexdigest()for n,v in m.items()},indent=1))
(E/'NHG_TAIL_CUT.json').write_text(json.dumps(dict(windows=3,cut='frontier(old); fields(nextRoot); frontier(new); Ok(out)',domain='1<=current.len<=815; one arbitrary callee pre/post window; prior and subsequent callee mutations only through their own windows and Lean composition',snapshot_borrow_fission='K040/K041 plus SnapshotViews.actual/carrier/frontier_ext; value-extensional CLOSED callees; no pointer-sensitive callee',overapproximation='initialized-tail suffix0..32/640, includes all raw/error child outcomes by proved envelopes; no child implementation claim'),indent=1))
