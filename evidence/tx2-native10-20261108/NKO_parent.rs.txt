//! NKO C03 exact tx2_common inactive call window; children are local oracles.
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct InactiveLog<'a>{proof:&'a[u8],reply:Option<E>,calls:usize}
impl InactiveLog<'_>{fn decode(&mut self,bytes:&[u8])->Option<E>{
 self.calls+=1;
 assert_eq!(bytes.as_ptr(),self.proof.as_ptr().wrapping_add(7495));
 assert_eq!(bytes.len(),32);
 let i=(kani::any::<u8>()&31) as usize;
 assert_eq!(bytes[i],self.proof[7495+i]^(if cfg!(NKO_invert){1}else{0}));
 self.reply
}}
// Literal source window: constants and ? are unchanged; only child is logged.
fn inactive_stage(proof:&[u8],log:&mut InactiveLog)->Result<E,Error>{
 let inactive=log.decode(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;
 Ok(inactive)
}
use aspis_core::field::{M31,CM31};
fn k(x:[u32;4])->K{K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn any_e()->E{let w:[u32;8]=kani::any();E::new(k([w[0],w[1],w[2],w[3]]),k([w[4],w[5],w[6],w[7]]))}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn inactive_call(){
 let bytes:[u8;57607]=kani::any();let len:usize=kani::any();kani::assume(7527<=len&&len<=57607);
 let proof=&bytes[..len];let reply=if kani::any(){Some(any_e())}else{None};
 let mut log=InactiveLog{proof,reply,calls:0};let out=inactive_stage(proof,&mut log);
 assert_eq!(log.calls,1);assert_eq!(out,reply.ok_or(Error::Parse));
 // Whole-proof dynamic frame mux retired after K002 timeout; payload only.
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn inactive_short_no_return(){
 let bytes:[u8;7527]=kani::any();let len:usize=kani::any();kani::assume(len<7527);
 let proof=if cfg!(NKO_short_control){&bytes[..]}else{&bytes[..len]};
 let mut log=InactiveLog{proof,reply:None,calls:0};let _=inactive_stage(proof,&mut log);
 assert!(false,"NKO short slice continuation is unreachable");
}

// C06: raw ownership return only, with no unrelated weight64 allocation.
fn pending_return(reply:Result<BatchedWeights,Error>)->Result<BatchedWeights,Error>{
 let pending=reply?;Ok(pending)
}
fn err(n:u8)->Error{match n%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pending_raw_return(){
 let cells:[[u64;4];64]=kani::any();let raw=Vec::from(cells);
 let ptr=raw.as_ptr();let cap=raw.capacity();let terms:usize=kani::any();
 let good:bool=kani::any();let error=err(kani::any());
 let reply=if good{Ok(BatchedWeights{raw,terms})}else{Err(error)};
 let result=pending_return(reply);
 match result{Err(e)=>{assert!(!good);assert_eq!(e,error);assert!(!cfg!(NKO_invert));},
 Ok(b)=>{assert!(good);assert_eq!(b.raw.as_ptr(),ptr);assert_eq!(b.raw.len(),64);assert_eq!(b.raw.capacity(),cap);assert_eq!(b.terms,terms);let i=(kani::any::<u8>()&63)as usize;let j=(kani::any::<u8>()&3)as usize;assert_eq!(b.raw[i][j],cells[i][j]^(if cfg!(NKO_invert){1}else{0}));}}
}

fn prepared()->Prepared{Prepared{variant:Variant::S2,roots:kani::any(),gamma:any_e(),kappa:any_e(),alpha:[any_e(),any_e()],rho:k(kani::any()),queries:kani::any(),semantic_alpha:core::array::from_fn(|_|k(kani::any())),z:[SecureCirclePoint{x:k(kani::any()),y:k(kani::any())},SecureCirclePoint{x:k(kani::any()),y:k(kani::any())}],claim:any_e(),state:kani::any()}}
fn geom(start:usize,cells:[[u32;5];12],lines:[u32;12])->QueryGeometry{
 QueryGeometry{start,inverses:Vec::from(cells.map(|r|r.map(M31))),line_z:Vec::from(lines.map(M31))}
}
struct QueryEntry<'a,const PART:usize>{proof:&'a[u8],words:&'a[[u32;4];64],rows:&'a[[u64;4];64],wp:*const K,wc:usize,rp:*const[u64;4],rc:usize,rhs:E,power:K,next:usize,terms:usize,calls:usize}
impl<const PART:usize> QueryEntry<'_,PART>{
 fn query(&mut self,proof:&[u8],_p:&Prepared,a:Accumulator,_g:&[E;29],_geometry:&QueryGeometry,pending:BatchedWeights,end:usize)->Result<(Accumulator,BatchedWeights),Error>{
 self.calls+=1;assert_eq!(self.calls,1);assert_eq!(end,22);
 if PART==0{assert_eq!(proof.as_ptr(),self.proof.as_ptr());assert_eq!(proof.len(),57607);let i=(kani::any::<u16>()&65535)as usize;kani::assume(i<57607);assert_eq!(proof[i],self.proof[i]^(if cfg!(NKO_invert){1}else{0}));}
 if PART==1{assert_eq!(a.weights.as_ptr(),self.wp);assert_eq!(a.weights.capacity(),self.wc);assert_eq!(a.weights.len(),64);let i=(kani::any::<u8>()&63)as usize;let j=(kani::any::<u8>()&3)as usize;let w=a.weights[i];let out=[w.c0.a.0,w.c0.b.0,w.c1.a.0,w.c1.b.0];assert_eq!(out[j],self.words[i][j]^(if cfg!(NKO_invert){1}else{0}));}
 if PART==2{assert_eq!(pending.raw.as_ptr(),self.rp);assert_eq!(pending.raw.capacity(),self.rc);assert_eq!(pending.raw.len(),64);let i=(kani::any::<u8>()&63)as usize;let j=(kani::any::<u8>()&3)as usize;assert_eq!(pending.raw[i][j],self.rows[i][j]^(if cfg!(NKO_invert){1}else{0}));}
 if PART==3{assert_eq!(a.rhs,self.rhs);assert_eq!(a.power,self.power);assert_eq!(a.next,self.next^(if cfg!(NKO_invert){1}else{0}));assert_eq!(pending.terms,self.terms);}
 // This is the incoming call cut. No returning/drop property is asserted.
 kani::assume(false);unreachable!()
 }}
fn query_entry<const PART:usize>(proof:&[u8],p:&Prepared,a:Accumulator,g:&[E;29],geometry:&QueryGeometry,pending:BatchedWeights,log:&mut QueryEntry<PART>)->Result<(Accumulator,BatchedWeights),Error>{
 let (a,pending)=log.query(proof,p,a,g,geometry,pending,22)?;Ok((a,pending))
}
fn query_input<const PART:usize>(){
 let proof:[u8;57607]=kani::any();let p=prepared();let gs:[[u32;8];29]=kani::any();let g=gs.map(|w|E::new(k([w[0],w[1],w[2],w[3]]),k([w[4],w[5],w[6],w[7]])));
 let cells:[[u32;5];12]=kani::any();let lines:[u32;12]=kani::any();let geometry=geom(kani::any(),cells,lines);
 let words:[[u32;4];64]=kani::any();let rows:[[u64;4];64]=kani::any();let weights=Vec::from(words.map(k));let raw=Vec::from(rows);
 let rhs=any_e();let power=k(kani::any());let next:usize=kani::any();let terms:usize=kani::any();
 let mut log=QueryEntry::<PART>{proof:&proof,words:&words,rows:&rows,wp:weights.as_ptr(),wc:weights.capacity(),rp:raw.as_ptr(),rc:raw.capacity(),rhs,power,next,terms,calls:0};
 let a=Accumulator{weights,rhs,power,next};let pending=BatchedWeights{raw,terms};let _=query_entry(&proof,&p,a,&g,&geometry,pending,&mut log);
}
#[kani::proof] #[kani::unwind(130)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn query_incoming_weights(){query_input::<1>();}
#[kani::proof] #[kani::unwind(130)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn query_incoming_raw(){query_input::<2>();}
#[kani::proof] #[kani::unwind(130)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn query_incoming_scalars(){query_input::<3>();}

#[kani::proof] #[kani::unwind(130)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn query_incoming_proof(){query_input::<0>();}

struct PendingFrame{reply:Option<Result<BatchedWeights,Error>>,calls:usize}
impl PendingFrame{fn pending(&mut self,_weights:&[K])->Result<BatchedWeights,Error>{self.calls+=1;self.reply.take().unwrap()}}
fn pending_weights_stage(weights:&[K],log:&mut PendingFrame)->Result<BatchedWeights,Error>{let pending=log.pending(weights)?;Ok(pending)}
#[kani::proof] #[kani::unwind(130)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pending_weights_frame(){
 let words:[[u32;4];64]=kani::any();let rows:[[u64;4];64]=kani::any();let weights=Vec::from(words.map(k));let raw=Vec::from(rows);let ptr=weights.as_ptr();let cap=weights.capacity();let good:bool=kani::any();let error=err(kani::any());let terms:usize=kani::any();let reply=if good{Ok(BatchedWeights{raw,terms})}else{Err(error)};
 let mut log=PendingFrame{reply:Some(reply),calls:0};let result=pending_weights_stage(&weights,&mut log);assert_eq!(log.calls,1);assert!(log.reply.is_none());assert_eq!(result.is_ok(),good);
 assert_eq!(weights.as_ptr(),ptr);assert_eq!(weights.capacity(),cap);assert_eq!(weights.len(),64);let i=(kani::any::<u8>()&63)as usize;let j=(kani::any::<u8>()&3)as usize;let w=weights[i];let out=[w.c0.a.0,w.c0.b.0,w.c1.a.0,w.c1.b.0];assert_eq!(out[j],words[i][j]^(if cfg!(NKO_invert){1}else{0}));
}
struct GeometryDrop{start:usize,inverse:*const[M31;5],ic:usize,line:*const M31,lc:usize,dropped:bool}
fn geometry_pending_stage(geometry:QueryGeometry,weights:&[K],log:&mut PendingFrame,drop_log:&mut GeometryDrop)->Result<(QueryGeometry,BatchedWeights),Error>{
 let pending=match log.pending(weights){Ok(pending)=>pending,Err(e)=>{
  drop_log.start=geometry.start;drop_log.inverse=geometry.inverses.as_ptr();drop_log.ic=geometry.inverses.capacity();drop_log.line=geometry.line_z.as_ptr();drop_log.lc=geometry.line_z.capacity();
  drop(geometry);drop_log.dropped=true;return Err(e);
 }};Ok((geometry,pending))
}
fn geometry_hold<const PART:usize>(){
 let cells:[[u32;5];12]=kani::any();let lines:[u32;12]=kani::any();let start:usize=kani::any();let geometry=geom(start,cells,lines);let ip=geometry.inverses.as_ptr();let ic=geometry.inverses.capacity();let lp=geometry.line_z.as_ptr();let lc=geometry.line_z.capacity();
 let words:[[u32;4];64]=kani::any();let weights=Vec::from(words.map(k));let rows:[[u64;4];64]=kani::any();let raw=Vec::from(rows);let good:bool=kani::any();let error=err(kani::any());let terms:usize=kani::any();let reply=if good{Ok(BatchedWeights{raw,terms})}else{Err(error)};let mut log=PendingFrame{reply:Some(reply),calls:0};let mut drops=GeometryDrop{start:0,inverse:core::ptr::null(),ic:0,line:core::ptr::null(),lc:0,dropped:false};
 let result=geometry_pending_stage(geometry,&weights,&mut log,&mut drops);assert_eq!(log.calls,1);assert!(log.reply.is_none());
 match result{Err(e)=>{assert!(!good);assert_eq!(e,error);assert!(drops.dropped);assert_eq!(drops.start,start);assert_eq!(drops.inverse,ip);assert_eq!(drops.ic,ic);assert_eq!(drops.line,lp);assert_eq!(drops.lc,lc);assert!(!cfg!(NKO_invert));},Ok((g,_pending))=>{assert!(good);assert!(!drops.dropped);
 if PART==0{assert_eq!(g.start,start^(if cfg!(NKO_invert){1}else{0}));}
 if PART==1{assert_eq!(g.inverses.as_ptr(),ip);assert_eq!(g.inverses.capacity(),ic);assert_eq!(g.inverses.len(),12);let i=(kani::any::<u8>()&15)as usize;kani::assume(i<12);let j=(kani::any::<u8>()&7)as usize;kani::assume(j<5);assert_eq!(g.inverses[i][j].0,cells[i][j]^(if cfg!(NKO_invert){1}else{0}));}
 if PART==2{assert_eq!(g.line_z.as_ptr(),lp);assert_eq!(g.line_z.capacity(),lc);assert_eq!(g.line_z.len(),12);let i=(kani::any::<u8>()&15)as usize;kani::assume(i<12);assert_eq!(g.line_z[i].0,lines[i]^(if cfg!(NKO_invert){1}else{0}));}
 }}
}
#[kani::proof] #[kani::unwind(130)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn geometry_pending_start(){geometry_hold::<0>();}
#[kani::proof] #[kani::unwind(130)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn geometry_pending_inverse(){geometry_hold::<1>();}
#[kani::proof] #[kani::unwind(130)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn geometry_pending_line(){geometry_hold::<2>();}
