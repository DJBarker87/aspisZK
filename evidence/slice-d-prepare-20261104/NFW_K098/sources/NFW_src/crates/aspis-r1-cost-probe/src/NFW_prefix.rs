use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
use crate::NFW_public::{Inputs,Hash};
fn allocation<T:Copy>(n:usize,_:T)->Result<Vec<T>,aspis_core::r0::Error>{assert_eq!(n,14759);Err(aspis_core::r0::Error::Allocation)}
fn resume_error<H:Digest32>(_:&[u8],_:&[u8],_:&[u8],v:Variant,_:H)->Result<(Box<Prepared>,Accumulator),Error>{assert_eq!(v,Variant::S2);Err(Error::Checkpoint)}
fn prepare_error(){let p=Inputs::new();let gword:u32=kani::any();kani::assume(gword<2147483647);let mut g=[E::from_limbs([gword;8]).unwrap();29];let out=prepare(p.public(kani::any()),&[],Hash,None,&mut g);assert!(matches!(out,Err(Error::Allocation))!=cfg!(NFW_invert));}
fn tx1_error(){let p=Inputs::new();let k:usize=kani::any();kani::assume(k!=10);let out=tx1(p.public(kani::any()),&[],&[],k,Hash,None);assert!(matches!(out,Err(Error::Parse))!=cfg!(NFW_invert));}
fn tx2_error(){let public:[u8;32]=kani::any();let proof:[u8;32]=kani::any();let checkpoint:[u8;32]=kani::any();let out=tx2_common(&public,&proof,&checkpoint,Hash,None);assert!(matches!(out,Err(Error::Checkpoint))!=cfg!(NFW_invert));}
use aspis_core::field::CM31;
fn spine_q()->K{K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn spine_e()->E{let w:[u32;8]=kani::any();let mut i=0;while i<8{kani::assume(w[i]<2147483647);i+=1;}E::from_limbs(w).unwrap()}
fn spine_qs<const N:usize>()->[K;N]{let mut out=[K::ZERO;N];let mut i=0;while i<N{out[i]=spine_q();i+=1;}out}
fn spine_es()->[E;29]{let mut out=[E::ZERO;29];let mut i=0;while i<29{out[i]=spine_e();i+=1;}out}
fn spine_sem(hash:Hash)->crate::r1_semantic::Verified<Hash>{
 let c=crate::r1_wire::Challenges{lambda:spine_q(),chi:spine_q(),theta:spine_q(),zc:spine_qs(),mu:spine_q(),eta:spine_q()};
 crate::r1_semantic::Verified{roots:kani::any(),challenges:c,alpha:spine_qs(),claims:Box::new([spine_qs(),spine_qs(),spine_qs()]),extra:spine_qs(),before_z1:spine_qs(),state_before_z0:kani::any(),z:[SecureCirclePoint{x:spine_q(),y:spine_q()},SecureCirclePoint{x:spine_q(),y:spine_q()}],transcript:crate::r1_wire::NFW_wire::seed(hash,kani::any(),kani::any())}
}
fn spine_prepared()->Prepared{Prepared{variant:Variant::S2,roots:kani::any(),gamma:spine_e(),kappa:spine_e(),alpha:[spine_e(),spine_e()],rho:spine_q(),queries:kani::any(),semantic_alpha:spine_qs(),z:[SecureCirclePoint{x:spine_q(),y:spine_q()},SecureCirclePoint{x:spine_q(),y:spine_q()}],claim:spine_e(),state:kani::any()}}
fn spine_error(n:u8)->Error{match n%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn public_address(p:Public<'_>)->(usize,usize,bool){match p{Public::Transfer(a,b)=>(a as *const _ as usize,b as *const _ as usize,false),Public::Withdrawal(a,b)=>(a as *const _ as usize,b as *const _ as usize,true)}}
struct SpineOps{fail:u8,error:Error,calls:usize,proof:usize,logical:usize,public:(usize,usize,bool),sem_address:usize,g_address:usize,inactive:E,sem:Option<crate::r1_semantic::Verified<Hash>>,prepared:Option<Box<Prepared>>,g:[E;29]}
impl SpineOps{
 fn heap(&mut self,n:usize,value:u8)->Result<Vec<u8>,aspis_core::r0::Error>{self.calls+=1;assert!(n==14759&&value==0);if self.fail==0{return Err(aspis_core::r0::Error::Allocation);}let logical=alloc::vec![0u8;n];self.logical=logical.as_ptr() as usize;Ok(logical)}
 fn expand_semantic(&mut self,src:&[u8],dst:&mut[u8])->Result<(),CodecError>{self.calls+=1;assert!(src.as_ptr() as usize==self.proof+16&&src.len()==7015&&dst.as_ptr() as usize==self.logical&&dst.len()==13831);if self.fail==1{Err(CodecError::Length)}else{Ok(())}}
 fn expand_values(&mut self,src:&[u8],dst:&mut[u8])->Result<(),CodecError>{self.calls+=1;assert!(src.as_ptr() as usize==self.proof+7031&&src.len()==464&&dst.as_ptr() as usize==self.logical+13831&&dst.len()==928);if self.fail==2{Err(CodecError::NonCanonical)}else{Ok(())}}
 fn wide_view<'a>(&mut self,proof:&'a[u8],semantic:&'a[u8],y1:&'a[u8])->Result<View<'a>,Error>{self.calls+=1;assert!(proof.as_ptr() as usize==self.proof&&proof.len()==57607&&semantic.as_ptr() as usize==self.logical&&semantic.len()==13831&&y1.as_ptr() as usize==self.logical+13831&&y1.len()==928);if self.fail==3{return Err(Error::Parse);}Ok(View{variant:Variant::S2,semantic,y1,inactive:self.inactive,round0:&proof[7527..7751],folded_root:Some((&proof[7751..7783]).try_into().unwrap()),round1:&proof[7783..8007],final_message:&proof[8007..10055],query_bytes:&[]})}
 fn verify(&mut self,public:Public<'_>,bytes:&[u8],_:Hash)->Result<crate::r1_semantic::Verified<Hash>,crate::r1_wire::Error>{self.calls+=1;assert!(public_address(public)==self.public&&bytes.as_ptr() as usize==self.logical&&bytes.len()==13831);if self.fail==4{{use crate::r1_wire::Error as W;let choice:u8=kani::any();let row:u8=kani::any();let actual:u8=kani::any();let value:usize=kani::any();Err(match choice%11{0=>W::Allocation,1=>W::RowOrder{expected:row,actual},2=>W::InvalidRow,3=>W::Tag{row},4=>W::Length{row},5=>W::NonCanonical{row,value},6=>W::Boundary{round:value},7=>W::Terminal,8=>W::EqualCirclePoints,9=>W::TrailingBytes,_=>W::Public})}}else{Ok(self.sem.take().unwrap())}}
 fn prepared(&mut self,sem:&crate::r1_semantic::Verified<Hash>,v:&View<'_>,_:Hash,g:&mut[E;29])->Result<Box<Prepared>,Error>{self.calls+=1;assert!((sem as *const _ as usize)==self.sem_address&&g.as_ptr() as usize==self.g_address&&v.variant==Variant::S2&&v.semantic.as_ptr() as usize==self.logical&&v.semantic.len()==13831&&v.y1.as_ptr() as usize==self.logical+13831&&v.y1.len()==928);*g=self.g;if self.fail==5{Err(self.error)}else{Ok(self.prepared.take().unwrap())}}
}
fn spine_body(public:Public<'_>,proof:&[u8],hash:Hash,obs:Observer,g:&mut[E;29],ops:&mut SpineOps)->Result<Box<Prepared>,Error>{

    let mut logical = ops.heap(compact::LOGICAL_SEMANTIC + compact::LOGICAL_Y1, 0u8).map_err(|_| Error::Allocation)?;
    let (semantic, y1) = logical.split_at_mut(compact::LOGICAL_SEMANTIC);
    ops.expand_semantic(&proof[compact::OFF_SEMANTIC..compact::OFF_Y1], semantic)?;
    ops.expand_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE], y1)?;
    let v = ops.wide_view(proof, &logical[..compact::LOGICAL_SEMANTIC], &logical[compact::LOGICAL_SEMANTIC..])?;
    let sem = ops.verify(public, v.semantic, hash).map_err(|_| Error::Semantic)?;
    ops.sem_address=&sem as *const _ as usize;
    mark(obs, Phase::Semantic);
    ops.prepared(&sem, &v, hash, g)

}
fn spine_check(){let inputs=Inputs::new();let public=inputs.public(kani::any());let proof:[u8;57607]=kani::any();let mut g=[E::ZERO;29];let p=Box::new(spine_prepared());let p_address=&*p as *const _ as usize;let fail:u8=kani::any();kani::assume(fail<=6);let mut ops=SpineOps{fail,error:spine_error(kani::any()),calls:0,proof:proof.as_ptr() as usize,logical:0,public:public_address(public),sem_address:0,g_address:g.as_ptr() as usize,inactive:spine_e(),sem:Some(spine_sem(Hash)),prepared:Some(p),g:spine_es()};let slot:usize=kani::any();let word:usize=kani::any();kani::assume(slot<29&&word<8);let expected_g=if fail<5{0}else{ops.g[slot].to_limbs()[word]};let out=spine_body(public,&proof,Hash,None,&mut g,&mut ops);let good=match out{Err(e)=>fail<6&&e==match fail{0=>Error::Allocation,1|2|3=>Error::Parse,4=>Error::Semantic,_=>ops.error},Ok(p)=>fail==6&&(&*p as *const _ as usize)==p_address};assert!((good&&ops.calls==(if fail<6{fail as usize+1}else{6})&&g[slot].to_limbs()[word]==expected_g)!=cfg!(NFW_invert));}
// Frozen TX prefixes with only child operations replaced by local records.
// Stops exactly at the query-loop boundary; checkpoint/finish are not entered.
struct TxOps{fail:u8,error:Error,calls:usize,proof:usize,public_bytes:usize,checkpoint:usize,public:(usize,usize,bool),p:Option<Box<Prepared>>,p_address:usize,p_queries_address:usize,p_gamma:E,g:[E;29],g_address:usize,weights_address:usize,raw_address:usize,geometry_address:usize,folded_address:usize,next:usize,stage2:bool}
impl TxOps{
 fn shape(&mut self,proof:&[u8])->Result<Variant,Error>{self.calls+=1;assert!(self.calls==1&&proof.as_ptr() as usize==self.proof&&proof.len()==57607);if self.fail==0{Err(Error::Parse)}else{Ok(Variant::S2)}}
 fn scan(&mut self,proof:&[u8])->Result<(),Error>{self.calls+=1;assert!(self.calls==2&&proof.as_ptr() as usize==self.proof);if self.fail==1{Err(Error::Parse)}else{Ok(())}}
 fn prepare(&mut self,public:Public<'_>,proof:&[u8],_:Hash,_:Observer,g:&mut[E;29])->Result<Box<Prepared>,Error>{self.calls+=1;assert!(self.calls==3&&public_address(public)==self.public&&proof.as_ptr() as usize==self.proof);self.g_address=g.as_ptr() as usize;*g=self.g;if self.fail==2{Err(self.error)}else{Ok(self.p.take().unwrap())}}
 fn accumulator(&mut self,v:Variant)->Result<Accumulator,Error>{self.calls+=1;assert!(self.calls==4&&v==Variant::S2);if self.fail==3{return Err(Error::Allocation);}let a=Accumulator{weights:alloc::vec![K::ZERO;64],rhs:E::ZERO,power:K::ONE,next:0};self.weights_address=a.weights.as_ptr() as usize;Ok(a)}
 fn merkle(&mut self,proof:&[u8],p:&Prepared,folded:&[u8;32],lo:usize,_:Hash)->Result<(),Error>{self.calls+=1;assert!(self.calls==(if self.stage2{4}else{5})&&proof.as_ptr() as usize==self.proof&&p as *const _ as usize==self.p_address&&folded.as_ptr() as usize==self.folded_address&&lo==(if self.stage2{1}else{0}));if self.fail==(if self.stage2{3}else{4}){Err(self.error)}else{Ok(())}}
 fn geometry(&mut self,queries:&[u32;22],lo:usize,hi:usize)->Result<QueryGeometry,Error>{self.calls+=1;assert!(self.calls==(if self.stage2{5}else{6})&&queries.as_ptr() as usize==self.p_queries_address&&lo==(if self.stage2{10}else{0})&&hi==(if self.stage2{22}else{10}));if self.fail==(if self.stage2{4}else{5}){Err(Error::Query)}else{Ok(QueryGeometry{start:lo,inverses:Vec::new(),line_z:Vec::new()})}}
 fn pending(&mut self,weights:&[K])->Result<BatchedWeights,Error>{self.calls+=1;assert!(self.calls==(if self.stage2{6}else{7})&&weights.as_ptr() as usize==self.weights_address&&weights.len()==64);if self.fail==(if self.stage2{5}else{6}){return Err(Error::Allocation);}let b=BatchedWeights{raw:alloc::vec![[0u64;4];64],terms:0};self.raw_address=b.raw.as_ptr() as usize;Ok(b)}
 fn query(&mut self,proof:&[u8],p:&Prepared,a:Accumulator,g:&[E;29],_:Observer,geometry:&QueryGeometry,b:BatchedWeights,k:usize)->Result<(Accumulator,BatchedWeights),Error>{self.calls+=1;let good=self.calls==(if self.stage2{7}else{8})&&proof.as_ptr() as usize==self.proof&&p as *const _ as usize==self.p_address&&a.weights.as_ptr() as usize==self.weights_address&&a.next==(if self.stage2{10}else{0})&&g.as_ptr() as usize==self.g_address&&geometry as *const _ as usize==self.geometry_address&&b.raw.as_ptr() as usize==self.raw_address&&b.terms==0&&k==(if self.stage2{22}else{10});assert!(good!=cfg!(NFW_invert));kani::assume(false);unreachable!()}
 fn resume(&mut self,checkpoint:&[u8],proof:&[u8],public_bytes:&[u8],v:Variant,_:Hash)->Result<(Box<Prepared>,Accumulator),Error>{self.calls+=1;assert!(self.calls==1&&checkpoint.as_ptr() as usize==self.checkpoint&&proof.as_ptr() as usize==self.proof&&public_bytes.as_ptr() as usize==self.public_bytes&&v==Variant::S2);if self.fail==0{return Err(Error::Checkpoint);}let a=Accumulator{weights:alloc::vec![K::ZERO;64],rhs:E::ZERO,power:K::ONE,next:self.next};self.weights_address=a.weights.as_ptr() as usize;Ok((self.p.take().unwrap(),a))}
 fn powers(&mut self,gamma:E)->[E;29]{self.calls+=1;assert!(self.calls==2);assert_eq!(gamma,self.p_gamma);self.g}
 fn inactive(&mut self,bytes:&[u8])->Option<E>{self.calls+=1;assert!(self.calls==3&&bytes.as_ptr() as usize==self.proof+7495&&bytes.len()==32);if self.fail==2{None}else{Some(E::ZERO)}}
}
fn tx1_prefix(public:Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize,hash:Hash,obs:Observer,ops:&mut TxOps)->Result<(),Error>{

    if k != SPLIT {
        return Err(Error::Parse);
    }
    ops.shape(proof)?;
    ops.scan(proof)?;
    mark(obs, Phase::Parsed);
    let mut g = [E::ZERO; 29];
    let p = ops.prepare(public, proof, hash, obs, &mut g)?;
    let a = ops.accumulator(Variant::S2)?;
    mark(obs, Phase::Prepare);
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    ops.folded_address=folded_root.as_ptr() as usize;
    ops.merkle(proof, &p, &folded_root, 0, hash)?;
    mark(obs, Phase::Merkle(0));
    let geometry = ops.geometry(&p.queries, 0, k)?;
    ops.geometry_address=&geometry as *const _ as usize;
    let pending = ops.pending(&a.weights)?;
    let (mut a, pending) = ops.query(proof, &p, a, &g, obs, &geometry, pending, k)?;

    Ok(())

}
fn tx2_prefix(public_bytes:&[u8],proof:&[u8],checkpoint:&[u8],hash:Hash,obs:Observer,ops:&mut TxOps)->Result<(),Error>{

    let (p, a) = ops.resume(checkpoint, proof, public_bytes, Variant::S2, hash)?;
    if a.next != SPLIT {
        return Err(Error::Checkpoint);
    }
    let g = ops.powers(p.gamma);
    ops.g_address=g.as_ptr() as usize;
    mark(obs, Phase::CheckpointRead);
    let inactive = ops.inactive(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    ops.folded_address=folded_root.as_ptr() as usize;
    ops.merkle(proof, &p, &folded_root, 1, hash)?;
    mark(obs, Phase::Merkle(SPLIT));
    let geometry = ops.geometry(&p.queries, a.next, 22)?;
    ops.geometry_address=&geometry as *const _ as usize;
    let pending = ops.pending(&a.weights)?;
    let (a, pending) = ops.query(proof, &p, a, &g, obs, &geometry, pending, 22)?;

    Ok(())

}
fn tx_context(public:Public<'_>,proof:&[u8],public_bytes:&[u8],checkpoint:&[u8],stage2:bool)->TxOps{let p=Box::new(spine_prepared());let p_address=&*p as *const _ as usize;let p_queries_address=p.queries.as_ptr() as usize;let p_gamma=p.gamma;let fail:u8=kani::any();kani::assume(fail<=7);TxOps{fail,error:spine_error(kani::any()),calls:0,proof:proof.as_ptr() as usize,public_bytes:public_bytes.as_ptr() as usize,checkpoint:checkpoint.as_ptr() as usize,public:public_address(public),p:Some(p),p_address,p_queries_address,p_gamma,g:spine_es(),g_address:0,weights_address:0,raw_address:0,geometry_address:0,folded_address:0,next:kani::any(),stage2}}
fn tx1_prefix_check(){let inputs=Inputs::new();let public=inputs.public(kani::any());let proof=alloc::vec![0u8;57607];let public_bytes:[u8;32]=kani::any();let mut ops=tx_context(public,&proof,&public_bytes,&[],false);let k:usize=kani::any();let result=tx1_prefix(public,&public_bytes,&proof,k,Hash,None,&mut ops);let good=match result{Err(e)=>if k!=10{e==Error::Parse&&ops.calls==0}else{e==match ops.fail{0|1=>Error::Parse,2|4=>ops.error,3|6=>Error::Allocation,5=>Error::Query,_=>ops.error}&&ops.calls==ops.fail as usize+1},Ok(_)=>false};assert!(good!=cfg!(NFW_invert));}
fn tx2_prefix_check(){let inputs=Inputs::new();let public=inputs.public(kani::any());let proof=alloc::vec![0u8;57607];let public_bytes:[u8;32]=kani::any();let checkpoint:[u8;32]=kani::any();let mut ops=tx_context(public,&proof,&public_bytes,&checkpoint,true);let result=tx2_prefix(&public_bytes,&proof,&checkpoint,Hash,None,&mut ops);let good=match result{Err(e)=>if ops.fail==0||ops.next!=10{e==Error::Checkpoint&&ops.calls==1}else{e==match ops.fail{2=>Error::Parse,3=>ops.error,4=>Error::Query,5=>Error::Allocation,_=>ops.error}&&ops.calls==ops.fail as usize+1},Ok(_)=>false};assert!(good!=cfg!(NFW_invert));}
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::proof] #[kani::unwind(258)]
fn prepare_error_root(){spine_check();}
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::proof] #[kani::unwind(258)]
fn prepare_error_root_renamed(){spine_check();}
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::proof] #[kani::unwind(258)]
fn tx1_error_root(){tx1_prefix_check();}
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::proof] #[kani::unwind(258)]
fn tx1_error_root_renamed(){tx1_prefix_check();}
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::proof] #[kani::unwind(258)]
fn tx2_error_root(){tx2_prefix_check();}
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::proof] #[kani::unwind(258)]
fn tx2_error_root_renamed(){tx2_prefix_check();}
