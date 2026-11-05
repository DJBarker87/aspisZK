"""Source-associated routing cut; not a child state/effects certificate."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
source=(E/'NHG_statement.rs.txt').read_text();start=source.index('            let p = self.semantic();',source.index('pub fn public_bytes(self)'));end=source.index('\n        }',start);original=source[start:end];body=original.replace('self.semantic()','public.semantic()').replace('fields(&mut out,','NHG_fields(&mut out,').replace('frontier(&mut out,','NHG_frontier(&mut out,').replace(')?;',',log)?;')
error=(E/'NHG_frontier.rs.txt').read_text();error=error[error.index('fn any_error()'):error.index('\n\n',error.index('fn any_error()'))]
sem=(E/'NHG_semantic.rs.txt').read_text();init=sem[sem.index(' let p=PoolV1'):sem.index(' let result=public.semantic()')]
s='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn digest()->Digest{let w:[u32;8]=kani::any();core::array::from_fn(|i|M31(w[i]))}
'''+error+'''
struct Log{calls:usize,window:usize,fail:bool,error:Error,seen:bool,frontier:bool,row:usize,word:usize,value:u32,length:usize,owner:*const alloc::vec::Vec<u8>}
fn NHG_fields(out:&mut alloc::vec::Vec<u8>,s:&[M31],log:&mut Log)->Result<(),Error>{let j=log.calls;log.calls+=1;if j==log.window{log.seen=true;log.frontier=false;log.length=s.len();log.value=s[log.word%s.len()].0;log.owner=out;if log.fail{return Err(log.error)}}Ok(())}
fn NHG_frontier(out:&mut alloc::vec::Vec<u8>,s:&[Digest;20],log:&mut Log)->Result<(),Error>{let j=log.calls;log.calls+=1;if j==log.window{log.seen=true;log.frontier=true;log.length=20;log.value=s[log.row][log.word].0;log.owner=out;if log.fail{return Err(log.error)}}Ok(())}
fn NHG_public_plan(public:Public<'_>,log:&mut Log)->Result<alloc::vec::Vec<u8>,Error>{
'''+body+'''
}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NHG_public_routing(){
'''+init+'''
 let window:usize=kani::any();kani::assume(window<8);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);let fail:bool=kani::any();let error=any_error();
 let mut log=Log{calls:0,window,fail,error,seen:false,frontier:false,row,word,value:0,length:0,owner:core::ptr::null()};
 let got=NHG_public_plan(public,&mut log);assert!(log.seen);assert_eq!(log.calls,if fail{window+1}else{8});
 let expected=match window{0=>if withdrawal{w.anchor_root[word].0}else{p.anchor_root[word].0},1=>if withdrawal{w.nullifier[word].0}else{p.nullifier[word].0},2=>if withdrawal{w.asset_id.0}else{p.asset_id.0},3=>if withdrawal{w.change_commitment[word].0}else{p.recipient_commitment[word].0},4=>if withdrawal{w.amount}else{p.change_commitment[word].0},5=>t.live_snapshot.frontier[row][word].0,6=>t.candidate_afterstate.next_root[word].0,_=>t.candidate_afterstate.next_frontier[row][word].0};
 assert_eq!(log.value,expected^if cfg!(NHG_invert){1}else{0});assert_eq!(log.frontier,window==5||window==7);assert_eq!(log.length,if window==5||window==7{20}else if window==2||(withdrawal&&window==4){1}else{8});
 match got{Err(e)=>{assert!(fail);assert_eq!(e,error)},Ok(out)=>{assert!(!fail);assert_eq!(out.len(),11);assert_eq!(out[0],if withdrawal{1}else{0});assert_eq!(out[1],if withdrawal{0}else{1});assert_eq!(out[2],if withdrawal{1}else{0});let k:usize=kani::any();kani::assume(k<8);assert_eq!(out[k+3],((t.live_snapshot.next_pair_index>>(8*k))&255)as u8);}}
}
'''
(E/'NHG_public_plan.rs.txt').write_text(s)
p=E/'NHG_statement.rs.txt';t=p.read_text();needle='    #[cfg(kani)] mod NHG_frontier {include!("NHG_frontier.rs");}\n';assert needle in t;p.write_text(t.replace(needle,needle+'    #[cfg(kani)] mod NHG_public_plan {include!("NHG_public_plan.rs");}\n'))
p=E/'NHG_OVERLAY.json';m=json.loads(p.read_text());m['crates/aspis-statement/src/pool_v1/NHG_public_plan.rs']='NHG_public_plan.rs.txt';p.write_text(json.dumps(m,indent=1))
(E/'NHG_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256((E/v).read_bytes()).hexdigest()for n,v in m.items()},indent=1))
(E/'NHG_PUBLIC_PLAN_CUT.json').write_text(json.dumps(dict(original=original,body=body,role='routing/control and Std literal/index bytes only; child state mutations are NOT credited by this harness',needed_composition='per-step full native window plus model frame chain, all child domains',branch_calls=8),indent=1))
