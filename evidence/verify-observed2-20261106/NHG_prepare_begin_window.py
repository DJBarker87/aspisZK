"""Fission one native callee window; retain original whole control certificate."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;G=E.parent/'verify-observed-20261105'
old=(G/'NGX_native.rs.txt').read_text();cut=json.loads((G/'NGX_BEGIN_CUT.json').read_text());body=cut['cut_body'].replace('begin_semantic_cut','NHG_begin_cut')
helpers=old[old.index('fn arbitrary_q()'):old.index('struct BeginLog')];error=old[old.index('fn any_error()'):old.index('struct ValidateLog')]
s='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]struct Hash(u64);
impl aspis_core::Digest32 for Hash{fn digest(&self,_:&[&[u8]])->[u8;32]{panic!("packet cuts only")}}
'''+helpers+error+'''
struct BeginLog{window:usize,calls:usize,seen:bool,fail:bool,error:Error,values:[QM31;15],after:[u8;32],next:u8,before:[u8;32],cursor:u8,row:u8,pointer:*const u8,length:usize}
fn NHG_begin_cut(t:&mut SemanticTranscript<Hash>,r:ValidatedRecord<'_>,log:&mut BeginLog)->Result<QM31,Error>{
 let j=log.calls;assert!(j<15);assert!(r.row<=24&&r.framed.len()<=3717);log.calls+=1;
 if j==log.window{
  log.seen=true;log.before=t.state;log.cursor=t.next_row;log.row=r.row;log.pointer=r.framed.as_ptr();log.length=r.framed.len();
  t.state=log.after;t.next_row=log.next;
  if log.fail{return Err(log.error)}
 }
 Ok(log.values[j])
}
fn NHG_begin_control(prefix:&Prefix<'_>,transcript:&mut SemanticTranscript<Hash>,log:&mut BeginLog)->Result<Challenges,Error>
'''+body+'''
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_begin_value(){
 let backing=alloc::vec![0u8;17000];let records:[&[u8];27]=core::array::from_fn(|_|{let start:usize=kani::any();let n:usize=kani::any();kani::assume(start<=13000&&n>=5&&n<=3717);&backing[start..start+n]});let root=(&backing[..32]).try_into().unwrap();let prefix=Prefix{c1_root:root,records};
 let window:usize=kani::any();kani::assume(window<15);let values:[QM31;15]=core::array::from_fn(|_|arbitrary_q());let after:[u8;32]=kani::any();let next:u8=kani::any();let fail:bool=kani::any();let error=any_error();
 let mut log=BeginLog{window,calls:0,seen:false,fail,error,values,after,next,before:[0;32],cursor:0,row:255,pointer:core::ptr::null(),length:0};
 let hash:u64=kani::any();let initial:[u8;32]=kani::any();let initial_cursor:u8=kani::any();let mut t=SemanticTranscript{state:initial,hash:Hash(hash),next_row:initial_cursor};
 let got=NHG_begin_control(&prefix,&mut t,&mut log);assert!(log.seen);assert_eq!(log.calls,if fail{window+1}else{15});
 let k:usize=kani::any();kani::assume(k<32);let z:usize=kani::any();kani::assume(z<10);
 assert_eq!(log.row as usize,window);assert_eq!(log.pointer,prefix.records[window].as_ptr());assert_eq!(log.length,prefix.records[window].len());assert_eq!(log.before[k],initial[k]);assert_eq!(log.cursor,initial_cursor);
 assert_eq!(t.state[k],after[k]);assert_eq!(t.next_row,next);assert_eq!(t.hash.0,hash);
 let correct=match got{Err(e)=>fail&&e==error,Ok(c)=>!fail&&c.lambda==values[0]&&c.chi==values[1]&&c.theta==values[2]&&c.mu==values[13]&&c.eta==values[14]&&c.zc[z]==values[3+z]};assert!(correct!=cfg!(NHG_invert));
}
'''
(E/'NHG_begin.rs.txt').write_text(s)
m=json.loads((E/'NHG_OVERLAY.json').read_text());(E/'NHG_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256((E/v).read_bytes()).hexdigest()for n,v in m.items()},indent=1))
(E/'NHG_BEGIN_WINDOW.json').write_text(json.dumps(dict(original=cut['original_body'],cut_body=body,windows=15,prestate='arbitrary full state32 and cursor at ONE callee window',native_credit='one-window only; other calls control/value cuts, never their state/effects',required_composition='Lean frame chain with each CLOSED semantic_validated packet; unchanged NGX K029/K030 global control'),indent=1))
