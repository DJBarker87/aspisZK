use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn e()->E {let v:[u32;8]=kani::any();for x in v {kani::assume(x<2147483647);}E::from_limbs(v).unwrap()}
fn k()->K {let v:[u32;4]=kani::any();for x in v {kani::assume(x<2147483647);}K{c0:CM31{a:M31(v[0]),b:M31(v[1])},c1:CM31{a:M31(v[2]),b:M31(v[3])}}}
fn ks<const N:usize>()->[K;N] {core::array::from_fn(|_|k())}
fn es<const N:usize>()->[E;N] {core::array::from_fn(|_|e())}
fn err()->Error {let n:u8=kani::any();kani::assume(n<8);match n{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn prepared()->Box<Prepared> {Box::new(Prepared{variant:Variant::S2,roots:kani::any(),gamma:e(),kappa:e(),alpha:es(),rho:k(),queries:kani::any(),semantic_alpha:ks(),z:core::array::from_fn(|_|SecureCirclePoint{x:k(),y:k()}),claim:e(),state:kani::any()})}
fn accumulator()->Accumulator {let values:[K;64]=ks();Accumulator{weights:Vec::from(values),rhs:e(),power:k(),next:kani::any()}}
fn kw(q:K,j:usize)->u32 {match j%4{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
fn pw(p:&Prepared,c:usize,i:usize,j:usize)->u32 {match c%14 {0=>p.roots[i%2][j%32] as u32,1=>p.gamma.to_limbs()[j%8],2=>p.kappa.to_limbs()[j%8],3=>p.alpha[i%2].to_limbs()[j%8],4=>kw(p.rho,j),5=>p.queries[i%22],6=>kw(p.semantic_alpha[i%10],j),7=>kw(p.z[i%2].x,j),8=>kw(p.z[i%2].y,j),9=>p.claim.to_limbs()[j%8],10=>p.state[j%32] as u32,_=>p.variant.tag() as u32}}
fn aw(a:&Accumulator,c:usize,i:usize,j:usize)->u64 {match c%6 {0=>kw(a.weights[i%64],j) as u64,1=>a.rhs.to_limbs()[j%8] as u64,2=>kw(a.power,j) as u64,3=>a.next as u64,4=>a.weights.len() as u64,_=>a.weights.as_ptr() as u64}}
fn selected()->(usize,usize,usize) {let c:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(c<14&&i<64&&j<32);(c,i,j)}
fn check(x:bool){assert!(x!=cfg!(NHV_invert));}
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{unreachable!()}}
struct ResumeLog {args:[usize;6],reply:Option<(Box<Prepared>,Accumulator)>,error:Option<Error>,calls:usize}
impl ResumeLog {fn resume(&mut self,checkpoint:&[u8],proof:&[u8],public:&[u8],variant:Variant,_:Hash)->Result<(Box<Prepared>,Accumulator),Error>{self.calls+=1;self.args=[checkpoint.as_ptr() as usize,checkpoint.len(),proof.as_ptr() as usize,proof.len(),public.as_ptr() as usize,public.len()];assert!(variant==Variant::S2);if let Some(x)=self.error {Err(x)}else{Ok(self.reply.take().unwrap())}}}
fn resume_cut(public_bytes:&[u8],proof:&[u8],checkpoint:&[u8],hash:Hash,ops:&mut ResumeLog)->Result<(Box<Prepared>,Accumulator),Error>{
 let (p,a)=ops.resume(checkpoint,proof,public_bytes,Variant::S2,hash)?;
 if a.next!=SPLIT {return Err(Error::Checkpoint);}
 Ok((p,a))
}
fn resume_check(){let p=prepared();let a=accumulator();let (c,i,j)=selected();let pv=pw(&p,c,i,j);let av=aw(&a,c,i,j);let addr=&*p as *const _ as usize;let next=a.next;let public:[u8;7]=kani::any();let proof:[u8;13]=kani::any();let cp:[u8;19]=kani::any();let error=if kani::any(){Some(err())}else{None};let mut log=ResumeLog{args:[0;6],reply:Some((p,a)),error,calls:0};let out=resume_cut(&public,&proof,&cp,Hash,&mut log);assert_eq!(log.args,[cp.as_ptr() as usize,19,proof.as_ptr() as usize,13,public.as_ptr() as usize,7]);let good=match out{Err(x)=>x==error.unwrap_or(Error::Checkpoint)&&(error.is_some()||next!=10),Ok((p,a))=>error.is_none()&&next==10&&(&*p as *const _ as usize)==addr&&pw(&p,c,i,j)==pv&&aw(&a,c,i,j)==av};check(good&&log.calls==1);}
struct PowersLog{gamma:E,reply:[E;29],calls:usize}
impl PowersLog{fn powers(&mut self,gamma:E)->[E;29]{self.calls+=1;self.gamma=gamma;self.reply}}
fn powers_cut(p:&Prepared,ops:&mut PowersLog)->[E;29]{let g=ops.powers(p.gamma);mark(None,Phase::CheckpointRead);g}
fn powers_check(){let p=prepared();let (c,i,j)=selected();let before=pw(&p,c,i,j);let reply:[E;29]=es();let selected=i%29;let expected=reply[selected];let mut log=PowersLog{gamma:E::ZERO,reply,calls:0};let g=powers_cut(&p,&mut log);check(log.gamma==p.gamma&&g[selected]==expected&&log.calls==1&&pw(&p,c,i,j)==before);}
struct GeometryLog{args:[usize;3],reply:Option<QueryGeometry>,error:Option<Error>,calls:usize}
impl GeometryLog{fn geometry(&mut self,queries:&[u32;22],lo:usize,hi:usize)->Result<QueryGeometry,Error>{self.calls+=1;self.args=[queries.as_ptr() as usize,lo,hi];if let Some(x)=self.error{Err(x)}else{Ok(self.reply.take().unwrap())}}}
fn geometry_cut(p:&Prepared,a:&Accumulator,ops:&mut GeometryLog)->Result<QueryGeometry,Error>{let geometry=ops.geometry(&p.queries,a.next,22)?;Ok(geometry)}
fn geometry_check(){let p=prepared();let a=accumulator();let (c,i,j)=selected();let pv=pw(&p,c,i,j);let av=aw(&a,c,i,j);let reply=QueryGeometry{start:kani::any(),inverses:Vec::from(core::array::from_fn::<[M31;5],12,_>(|_|core::array::from_fn(|_|M31(kani::any())))),line_z:Vec::from(core::array::from_fn::<M31,12,_>(|_|M31(kani::any())))};let start=reply.start;let inv=reply.inverses.as_ptr() as usize;let z=reply.line_z.as_ptr() as usize;let ix=i%12;let val=reply.inverses[ix];let zv=reply.line_z[ix];let error=if kani::any(){Some(err())}else{None};let mut log=GeometryLog{args:[0;3],reply:Some(reply),error,calls:0};let out=geometry_cut(&p,&a,&mut log);let good=match out{Err(x)=>Some(x)==error,Ok(g)=>error.is_none()&&g.start==start&&g.inverses.as_ptr() as usize==inv&&g.line_z.as_ptr() as usize==z&&g.inverses[ix]==val&&g.line_z[ix]==zv};check(good&&log.args==[p.queries.as_ptr() as usize,a.next,22]&&log.calls==1&&pw(&p,c,i,j)==pv&&aw(&a,c,i,j)==av);}
struct PendingLog{args:[usize;2],reply:Option<BatchedWeights>,error:Option<Error>,calls:usize}
impl PendingLog{fn pending(&mut self,weights:&[K])->Result<BatchedWeights,Error>{self.calls+=1;self.args=[weights.as_ptr() as usize,weights.len()];if let Some(x)=self.error{Err(x)}else{Ok(self.reply.take().unwrap())}}}
fn pending_cut(a:&Accumulator,ops:&mut PendingLog)->Result<BatchedWeights,Error>{let pending=ops.pending(&a.weights)?;Ok(pending)}
fn pending_check(){let a=accumulator();let (c,i,j)=selected();let av=aw(&a,c,i,j);let reply=BatchedWeights{raw:Vec::from(kani::any::<[[u64;4];64]>()),terms:kani::any()};let addr=reply.raw.as_ptr() as usize;let raw=reply.raw[i][j%4];let terms=reply.terms;let error=if kani::any(){Some(err())}else{None};let mut log=PendingLog{args:[0;2],reply:Some(reply),error,calls:0};let out=pending_cut(&a,&mut log);let good=match out{Err(x)=>Some(x)==error,Ok(b)=>error.is_none()&&b.raw.as_ptr() as usize==addr&&b.raw.len()==64&&b.raw[i][j%4]==raw&&b.terms==terms};check(good&&log.args==[a.weights.as_ptr() as usize,64]&&log.calls==1&&aw(&a,c,i,j)==av);}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn resume_slot(){resume_check();}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn resume_slot_renamed(){resume_check();}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn powers_slot(){powers_check();}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn powers_slot_renamed(){powers_check();}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn geometry_slot(){geometry_check();}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn geometry_slot_renamed(){geometry_check();}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pending_slot(){pending_check();}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pending_slot_renamed(){pending_check();}
