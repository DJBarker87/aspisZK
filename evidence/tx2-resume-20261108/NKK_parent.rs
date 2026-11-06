// Source-ordered resume segment cuts. Frozen body: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
// Child Reader methods are local full-reply oracles under ruling (y).
use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
struct RawOracle<'a,const N:usize,const C:usize>{
 bytes:&'a[u8],at:usize,replies:[[u8;N];C],posts:[usize;C],calls:usize,
 seen:[usize;C],ptrs:[*const u8;C],lens:[usize;C],frame:[u8;C],observe:usize,
}
impl<const N:usize,const C:usize> RawOracle<'_,N,C>{
 fn raw(&mut self)->[u8;N]{
  let i=self.calls;assert!(i<C);self.calls+=1;
  self.seen[i]=self.at;self.ptrs[i]=self.bytes.as_ptr();self.lens[i]=self.bytes.len();
  self.frame[i]=self.bytes[self.observe];self.at=self.posts[i];self.replies[i]
 }
}
// Each query chunk is a literal contiguous subsequence of resume's initializer.
fn query8(r:&mut RawOracle<4,8>)->[u32;8]{[
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw())]}
fn query6(r:&mut RawOracle<4,6>)->[u32;6]{[
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw())]}
fn raw_pre<const N:usize,const C:usize>(bytes:&[u8;1768])->RawOracle<'_,N,C>{
 let observe:usize=kani::any();kani::assume(observe<1768);
 RawOracle{bytes,at:kani::any(),replies:kani::any(),posts:kani::any(),calls:0,
 seen:[0;C],ptrs:[core::ptr::null();C],lens:[0;C],frame:[0;C],observe}
}
fn frame<const N:usize,const C:usize>(r:&RawOracle<N,C>,start:usize,bytes:&[u8;1768]){
 assert_eq!(r.calls,C);assert_eq!(r.at,r.posts[C-1]);
 let j:usize=kani::any();kani::assume(j<C);
 let expect=if j==0{start}else{r.posts[j-1]};
 assert_eq!(r.seen[j],expect^(if cfg!(NKK_bad_backing){1}else{0}));
 assert_eq!(r.ptrs[j],bytes.as_ptr());assert_eq!(r.lens[j],1768);
 assert_eq!(r.frame[j],bytes[r.observe]);assert_eq!(r.bytes[r.observe],bytes[r.observe]);
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn query_chunk8(){
 let bytes:[u8;1768]=kani::any();let mut r=raw_pre::<4,8>(&bytes);let start=r.at;
 let out=query8(&mut r);frame(&r,start,&bytes);
 let j:usize=kani::any();kani::assume(j<8);
 assert_eq!(out[j],u32::from_le_bytes(r.replies[j])^(if cfg!(NKK_invert){1}else{0}));
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn query_chunk6(){
 let bytes:[u8;1768]=kani::any();let mut r=raw_pre::<4,6>(&bytes);let start=r.at;
 let out=query6(&mut r);frame(&r,start,&bytes);
 let j:usize=kani::any();kani::assume(j<6);
 assert_eq!(out[j],u32::from_le_bytes(r.replies[j])^(if cfg!(NKK_invert){1}else{0}));
}
// Literal state/root segment of resume, with exact source evaluation order.
fn roots(r:&mut RawOracle<32,3>)->([u8;32],[[u8;32];2]){
 let state=r.raw();let roots=[r.raw(),r.raw()];(state,roots)
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn state_roots_stage(){
 let bytes:[u8;1768]=kani::any();let mut r=raw_pre::<32,3>(&bytes);let start=r.at;
 let (state,roots)=roots(&mut r);frame(&r,start,&bytes);
 let j:usize=kani::any();kani::assume(j<32);
 assert_eq!(state[j],r.replies[0][j]^(if cfg!(NKK_invert){1}else{0}));
 assert_eq!(roots[0][j],r.replies[1][j]);assert_eq!(roots[1][j],r.replies[2][j]);
}
fn nk(x:[u32;4])->K{use aspis_core::field::{CM31,M31};K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn ne(w:[u32;8])->E{E::new(nk([w[0],w[1],w[2],w[3]]),nk([w[4],w[5],w[6],w[7]]))}
fn kw(k:K)->[u32;4]{[k.c0.a.0,k.c0.b.0,k.c1.a.0,k.c1.b.0]}
fn err(n:u8)->Error{match n%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
struct FieldOracle<'a,const C:usize>{
 bytes:&'a[u8],at:usize,values:[[u32;8];C],errors:[bool;C],codes:[u8;C],posts:[usize;C],
 calls:usize,seen:[usize;C],kinds:[u8;C],ptrs:[*const u8;C],lens:[usize;C],frame:[u8;C],observe:usize,
}
impl<const C:usize> FieldOracle<'_,C>{
 fn read(&mut self,kind:u8)->Result<[u32;8],Error>{
  let i=self.calls;assert!(i<C);self.calls+=1;self.seen[i]=self.at;self.kinds[i]=kind;
  self.ptrs[i]=self.bytes.as_ptr();self.lens[i]=self.bytes.len();self.frame[i]=self.bytes[self.observe];
  self.at=self.posts[i];if self.errors[i]{Err(err(self.codes[i]))}else{Ok(self.values[i])}
 }
 fn e(&mut self)->Result<E,Error>{Ok(ne(self.read(32)?))}
 fn k(&mut self)->Result<K,Error>{let w=self.read(16)?;Ok(nk([w[0],w[1],w[2],w[3]]))}
}
fn field_pre<const C:usize>(bytes:&[u8;1768])->FieldOracle<'_,C>{
 let observe:usize=kani::any();kani::assume(observe<1768);
 FieldOracle{bytes,at:kani::any(),values:kani::any(),errors:kani::any(),codes:kani::any(),posts:kani::any(),calls:0,seen:[0;C],kinds:[0;C],ptrs:[core::ptr::null();C],lens:[0;C],frame:[0;C],observe}
}
fn field_frame<const C:usize>(r:&FieldOracle<C>,start:usize,bytes:&[u8;1768],kinds:[u8;C])->Option<Error>{
 let mut calls=C;let mut error=None;
 for i in 0..C{if r.errors[i]{calls=i+1;error=Some(err(r.codes[i]));break;}}
 assert_eq!(r.calls,calls);assert_eq!(r.at,r.posts[calls-1]);
 let j:usize=kani::any();kani::assume(j<calls);
 assert_eq!(r.seen[j],(if j==0{start}else{r.posts[j-1]})^(if cfg!(NKK_bad_backing){1}else{0}));
 assert_eq!(r.kinds[j],kinds[j]);assert_eq!(r.ptrs[j],bytes.as_ptr());assert_eq!(r.lens[j],1768);
 assert_eq!(r.frame[j],bytes[r.observe]);assert_eq!(r.bytes[r.observe],bytes[r.observe]);error
}
// Literal contiguous field-read segment, with every Result arm from the oracle.
fn gamma(r:&mut FieldOracle<5>)->Result<(E,E,[E;2],K),Error>{
 let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];let rho=r.k()?;
 Ok((gamma,kappa,alpha,rho))
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn gamma_stage(){
 let bytes:[u8;1768]=kani::any();let mut r=field_pre::<5>(&bytes);let start=r.at;
 let out=gamma(&mut r);let error=field_frame(&r,start,&bytes,[32,32,32,32,16]);
 assert_eq!(out.is_ok(),error.is_none()^cfg!(NKK_invert));
 match out{Err(e)=>assert_eq!(Some(e),error),Ok((g,k,a,rho))=>{
 assert_eq!(g.to_limbs(),ne(r.values[0]).to_limbs());assert_eq!(k.to_limbs(),ne(r.values[1]).to_limbs());
 assert_eq!(a[0].to_limbs(),ne(r.values[2]).to_limbs());assert_eq!(a[1].to_limbs(),ne(r.values[3]).to_limbs());
 assert_eq!(kw(rho),[r.values[4][0],r.values[4][1],r.values[4][2],r.values[4][3]]);}}
}
fn z_claim(r:&mut FieldOracle<7>)->Result<([SecureCirclePoint;2],E,E,K),Error>{
 let z=[SecureCirclePoint{x:r.k()?,y:r.k()?},SecureCirclePoint{x:r.k()?,y:r.k()?}];
 let claim=r.e()?;let rhs=r.e()?;let power=r.k()?;Ok((z,claim,rhs,power))
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn z_claim_stage(){
 let bytes:[u8;1768]=kani::any();let mut r=field_pre::<7>(&bytes);let start=r.at;
 let out=z_claim(&mut r);let error=field_frame(&r,start,&bytes,[16,16,16,16,32,32,16]);
 assert_eq!(out.is_ok(),error.is_none()^cfg!(NKK_invert));
 match out{Err(e)=>assert_eq!(Some(e),error),Ok((z,c,rhs,p))=>{
 let i:usize=kani::any();kani::assume(i<4);let seen=[kw(z[0].x),kw(z[0].y),kw(z[1].x),kw(z[1].y)];
 assert_eq!(seen[i],[r.values[i][0],r.values[i][1],r.values[i][2],r.values[i][3]]);
 assert_eq!(c.to_limbs(),ne(r.values[4]).to_limbs());assert_eq!(rhs.to_limbs(),ne(r.values[5]).to_limbs());
 assert_eq!(kw(p),[r.values[6][0],r.values[6][1],r.values[6][2],r.values[6][3]]);}}
}
struct SemanticLog<'a>{reply:Option<Result<([K;10],usize),Error>>,bytes:&'a[u8],calls:usize,seen_at:usize,seen_ptr:*const u8,seen_len:usize,observe:usize,seen_byte:u8}
impl SemanticLog<'_>{fn semantic(&mut self,bytes:&[u8],at:usize)->Result<([K;10],usize),Error>{
 self.calls+=1;self.seen_at=at;self.seen_ptr=bytes.as_ptr();self.seen_len=bytes.len();self.seen_byte=bytes[self.observe];self.reply.take().unwrap()
}}
// Source semantic return/writeback and immediately following z.x read.
fn semantic_z(bytes:&[u8],r:&mut FieldOracle<1>,log:&mut SemanticLog)->Result<([K;10],K),Error>{
 let (semantic_alpha,at)=log.semantic(bytes,r.at)?;
 r.at=at^(if cfg!(NKK_bad_view){1}else{0});
 let zx=r.k()?;Ok((semantic_alpha,zx))
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn semantic_writeback_stage(){
 let bytes:[u8;1768]=kani::any();let mut r=field_pre::<1>(&bytes);let start=r.at;
 let values:[K;10]=core::array::from_fn(|_|nk(kani::any()));let post:usize=kani::any();let se:bool=kani::any();let code:u8=kani::any();
 let reply=if se{Err(err(code))}else{Ok((values,post))};
 let mut log=SemanticLog{reply:Some(reply),bytes:&bytes,calls:0,seen_at:0,seen_ptr:core::ptr::null(),seen_len:0,observe:r.observe,seen_byte:0};
 let out=semantic_z(&bytes,&mut r,&mut log);
 assert_eq!(log.calls,1);assert!(log.reply.is_none());assert_eq!(log.seen_at,start);assert_eq!(log.seen_ptr,bytes.as_ptr());assert_eq!(log.seen_len,1768);assert_eq!(log.seen_byte,bytes[log.observe]);
 assert_eq!(log.bytes[log.observe],bytes[log.observe]);
 assert_eq!(out.is_ok(),(!se&&!r.errors[0])^cfg!(NKK_invert));
 if se{assert_eq!(r.calls,0);assert_eq!(r.at,start);assert_eq!(out.unwrap_err(),err(code));}
 else{let error=field_frame(&r,post,&bytes,[16]);match out{Err(e)=>assert_eq!(Some(e),error),Ok((a,z))=>{
 let j:usize=kani::any();kani::assume(j<10);assert_eq!(kw(a[j]),kw(values[j]));assert_eq!(kw(z),[r.values[0][0],r.values[0][1],r.values[0][2],r.values[0][3]]);}}}
}
// The terminal guard owns the SAME returned weights. Native Vec drop executes
// in the rejection branch; the log marks the source cleanup site, not a new
// allocator-value theorem. Pinned std/allocator semantics retain that boundary.
struct TailLog{dropped:bool,ptr:*const K,len:usize,cap:usize,prepared_calls:usize}
fn tail(weights:alloc::vec::Vec<K>,at:usize,end:usize,log:&mut TailLog)->Result<alloc::vec::Vec<K>,Error>{
 if at!=end{
  log.ptr=weights.as_ptr();log.len=weights.len();log.cap=weights.capacity();
  if cfg!(NKK_bad_drop){core::mem::forget(weights);}else{drop(weights);log.dropped=true;}
  return Err(Error::Checkpoint);
 }
 Ok(weights)
}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn owned_tail_stage(){
 let before:[[u32;4];64]=kani::any();let j:usize=kani::any();kani::assume(j<64);
 let mut weights=alloc::vec::Vec::with_capacity(64);for v in before{weights.push(nk(v));}
 let ptr=weights.as_ptr();let cap=weights.capacity();let at:usize=kani::any();let end=1736usize;
 let mut log=TailLog{dropped:false,ptr:core::ptr::null(),len:0,cap:0,prepared_calls:0};
 let out=tail(weights,at,end,&mut log);assert_eq!(log.prepared_calls,0);
 assert_eq!(out.is_ok(),(at==end)^cfg!(NKK_invert));
 match out{Err(e)=>{assert_eq!(e,Error::Checkpoint);assert!(log.dropped);assert_eq!(log.ptr,ptr);assert_eq!(log.len,64);assert_eq!(log.cap,cap);},Ok(w)=>{
 assert!(!log.dropped);assert_eq!(w.as_ptr(),ptr);assert_eq!(w.len(),64);assert_eq!(w.capacity(),cap);assert_eq!(kw(w[j]),before[j]);}}
}
// Exact first header conditional, with a local ghost counter in the native any.
fn header(bytes:&[u8;16],len:usize,scanned:&mut usize)->Result<(),Error>{
 if len!=checkpoint_size(Variant::S2)||&bytes[..8]!=b"R1P2CKP2"||bytes[8]!=Variant::S2.tag()||bytes[9]>22||bytes[10]!=1||bytes[11..16].iter().any(|&b|{*scanned+=1;b!=0}){return Err(Error::Checkpoint);}
 Ok(())
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn header_prefix_stage(){
 let bytes:[u8;16]=kani::any();let len:usize=kani::any();let mut scanned=0;
 let entered=len==1768&&bytes[..8]==*b"R1P2CKP2"&&bytes[8]==2&&bytes[9]<=22&&bytes[10]==1;
 let mut expected=0;let mut nonzero=false;
 if entered{for i in 11..16{expected+=1;if bytes[i]!=0{nonzero=true;break;}}}
 let out=header(&bytes,len,&mut scanned);
 assert_eq!(scanned,expected^(if cfg!(NKK_bad_backing){1}else{0}));
 assert_eq!(out.is_ok(),(entered&&!nonzero)^cfg!(NKK_invert));
 if out.is_err(){assert_eq!(out,Err(Error::Checkpoint));}
}
struct DigestStageLog<'a>{expected:&'a[u8],checkpoint:&'a[u8],reply:[u8;32],seen_ptr:*const u8,seen_len:usize,calls:usize,observe:usize,seen_byte:Option<u8>,second_ptr:*const u8,second_len:usize,second_byte:u8,second_observe:usize}
impl DigestStageLog<'_>{fn digest(&mut self,parts:&[&[u8]],kind:usize)->[u8;32]{
 self.calls+=1;assert_eq!(parts.len(),if kind==2{2}else{1});
 self.seen_ptr=parts[0].as_ptr();self.seen_len=parts[0].len();self.seen_byte=parts[0].get(self.observe).copied();
 if kind==2{assert_eq!(parts[0],b"UNPROVED:R1:checkpoint");self.second_ptr=parts[1].as_ptr();self.second_len=parts[1].len();self.second_byte=parts[1][self.second_observe];}
 self.reply
}}
fn digest_stage(bytes:&[u8;1768],input:&[u8],kind:usize,log:&mut DigestStageLog)->Result<(),Error>{
 let digest=if kind==2{log.digest(&[b"UNPROVED:R1:checkpoint",&bytes[if cfg!(NKK_bad_view){1}else{0}..1736]],kind)}else{log.digest(&[input],kind)};
 let expected=if kind==0{&bytes[16..48]}else if kind==1{&bytes[48..80]}else{&bytes[1736..]};
 if expected!=digest{return Err(Error::Checkpoint);}Ok(())
}
fn digest_window<const C:usize>(kind:usize){
 let bytes:[u8;1768]=kani::any();let backing:[u8;C]=kani::any();let plen:usize=if kind==1{kani::any()}else{C};kani::assume(plen<=C);let input=&backing[..plen];let reply:[u8;32]=kani::any();
 let observe:usize=kani::any();kani::assume(observe<if kind==2{22}else{C});
 let second_observe:usize=kani::any();kani::assume(second_observe<1736);
 let expected_input=if kind==2{&b"UNPROVED:R1:checkpoint"[..]}else{&input[..]};
 let mut log=DigestStageLog{expected:expected_input,checkpoint:&bytes,reply,seen_ptr:core::ptr::null(),seen_len:0,calls:0,observe,seen_byte:None,second_ptr:core::ptr::null(),second_len:0,second_byte:0,second_observe};
 let out=digest_stage(&bytes,&input,kind,&mut log);
 assert_eq!(log.calls,1);assert_eq!(log.seen_ptr,log.expected.as_ptr());assert_eq!(log.seen_len,log.expected.len());assert_eq!(log.seen_byte,log.expected.get(observe).copied());
 if kind==2{assert_eq!(log.second_ptr,bytes.as_ptr());assert_eq!(log.second_len,1736);assert_eq!(log.second_byte,bytes[second_observe]);}
 assert_eq!(log.checkpoint[second_observe],bytes[second_observe]);
 let same=if kind==0{bytes[16..48]==reply}else if kind==1{bytes[48..80]==reply}else{bytes[1736..]==reply};
 assert_eq!(out.is_ok(),same^cfg!(NKK_invert));
 if out.is_err(){assert_eq!(out,Err(Error::Checkpoint));}
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn proof_digest_stage(){digest_window::<57607>(0);}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn public_digest_stage(){digest_window::<1880>(1);}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn checkpoint_digest_stage(){digest_window::<22>(2);}
fn prepared()->Prepared{
 Prepared{variant:Variant::S2,roots:kani::any(),gamma:ne(kani::any()),kappa:ne(kani::any()),alpha:[ne(kani::any()),ne(kani::any())],rho:nk(kani::any()),queries:kani::any(),semantic_alpha:core::array::from_fn(|_|nk(kani::any())),z:[SecureCirclePoint{x:nk(kani::any()),y:nk(kani::any())},SecureCirclePoint{x:nk(kani::any()),y:nk(kani::any())}],claim:ne(kani::any()),state:kani::any()}
}
// Final return expression with the already assembled SAME Prepared fields.
fn return_pair(p:Prepared,weights:alloc::vec::Vec<K>,rhs:E,power:K,next:u8)->Result<(Box<Prepared>,Accumulator),Error>{
 Ok((Box::new(p),Accumulator{weights,rhs,power,next:next as usize}))
}
fn pair_window<const W:u8>(){
 let p=prepared();let roots=p.roots;let state=p.state;let fields=[p.gamma,p.kappa,p.alpha[0],p.alpha[1],p.claim];let rho=p.rho;let queries=p.queries;let semantic=p.semantic_alpha;let z=p.z;
 let before:[[u32;4];64]=kani::any();let mut weights=alloc::vec::Vec::with_capacity(64);for v in before{weights.push(nk(v));}
 let ptr=weights.as_ptr();let cap=weights.capacity();let rhs=ne(kani::any());let power=nk(kani::any());let next:u8=kani::any();
 let (p,mut a)=return_pair(p,weights,rhs,power,next).unwrap();
 if cfg!(NKK_bad_alloc){let mut other=alloc::vec::Vec::with_capacity(64);for v in before{other.push(nk(v));}a.weights=other;}
 assert!(p.variant==Variant::S2);assert_eq!(a.weights.as_ptr(),ptr);assert_eq!(a.weights.len(),64);assert_eq!(a.weights.capacity(),cap);
 if W==0{
 let j:usize=kani::any();kani::assume(j<32);assert_eq!(p.roots[0][j],roots[0][j]);assert_eq!(p.roots[1][j],roots[1][j]);assert_eq!(p.state[j],state[j]);
 assert_eq!([p.gamma,p.kappa,p.alpha[0],p.alpha[1],p.claim],fields);
 let mut expected=kw(rho);if cfg!(NKK_invert){expected[0]^=1;}assert_eq!(kw(p.rho),expected);
 assert_eq!(p.z[0].x,z[0].x);assert_eq!(p.z[0].y,z[0].y);assert_eq!(p.z[1].x,z[1].x);assert_eq!(p.z[1].y,z[1].y);
 }
 if W==1{
 let qi:usize=kani::any();let si:usize=kani::any();kani::assume(qi<22&&si<10);
 assert_eq!(p.queries[qi],queries[qi]^(if cfg!(NKK_invert){1}else{0}));assert_eq!(p.semantic_alpha[si],semantic[si]);
 }
 if W==2{
 let j:usize=kani::any();kani::assume(j<64);let mut expected=before[j];if cfg!(NKK_invert){expected[0]^=1;}
 assert_eq!(kw(a.weights[j]),expected);assert_eq!(a.rhs,rhs);assert_eq!(a.power,power);assert_eq!(a.next,next as usize);
 }
}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pair_scalar_window(){pair_window::<0>();}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pair_array_window(){pair_window::<1>();}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pair_owned_window(){pair_window::<2>();}
// Changed K031 shape: dynamic modifies instrumentation protects the complete
// proof slice without enumerating a symbolic byte into its57607-byte array.
struct Descriptor{calls:usize,ptr:*const u8,len:usize,reply:[u8;32]}
impl Descriptor{fn digest(&mut self,input:&[u8])->[u8;32]{self.calls+=1;self.ptr=input.as_ptr();self.len=input.len();self.reply}}
impl kani::Arbitrary for Error{fn any()->Self{err(kani::any())}}
#[kani::requires(log.calls==0 && proof.len()==57607)]
#[kani::ensures(|out| (out.is_ok() || *out==Err(Error::Parse))^cfg!(NKK_invert))]
#[kani::modifies(&mut log.calls)]
fn slice_fidelity_weak(proof:&[u8],log:&mut Descriptor)->Result<(),Error>{let _=proof.len();log.calls=1;Ok(())}
#[kani::proof_for_contract(slice_fidelity_weak)]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn slice_fidelity_contract(){let bytes:[u8;57607]=kani::any();let mut log=Descriptor{calls:0,ptr:core::ptr::null(),len:0,reply:kani::any()};let _=slice_fidelity_weak(&bytes,&mut log);}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn slice_fidelity_real(){let bytes:[u8;57607]=kani::any();let mut log=Descriptor{calls:0,ptr:core::ptr::null(),len:0,reply:kani::any()};let out=slice_fidelity_weak(&bytes,&mut log);assert!(out.is_ok());}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub_verified(slice_fidelity_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn slice_fidelity_unimplied(){let bytes:[u8;57607]=kani::any();let mut log=Descriptor{calls:0,ptr:core::ptr::null(),len:0,reply:kani::any()};let out=slice_fidelity_weak(&bytes,&mut log);assert!(out.is_ok());}
#[kani::requires(log.calls==0 && proof.len()==57607)]
#[kani::ensures(|out| out.is_ok())]
#[kani::modifies(&mut log.calls)]
fn slice_fidelity_modifies(proof:&[u8],log:&mut Descriptor)->Result<(),Error>{let _=proof.len();log.calls=1;if cfg!(NKK_bad_reply){log.reply[0]^=1;}Ok(())}
#[kani::proof_for_contract(slice_fidelity_modifies)]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn slice_fidelity_modifies_check(){let bytes:[u8;57607]=kani::any();let mut log=Descriptor{calls:0,ptr:core::ptr::null(),len:0,reply:kani::any()};let _=slice_fidelity_modifies(&bytes,&mut log);}
#[kani::requires(log.calls==0 && proof.len()==57607 && stored.len()==32)]
#[kani::ensures(|out| *out==if stored!=log.reply{Err(Error::Checkpoint)}else{Ok(())})]
#[kani::ensures(|_| log.calls==1 && log.ptr==proof.as_ptr() && log.len==proof.len() && !cfg!(NKK_invert))]
#[kani::modifies(&mut log.calls,&mut log.ptr,&mut log.len)]
fn proof_digest_frame_cut(stored:&[u8],proof:&[u8],log:&mut Descriptor)->Result<(),Error>{
 let reply=log.digest(if cfg!(NKK_bad_view){&proof[1..]}else{proof});
 if cfg!(NKK_bad_reply){log.reply[0]^=1;}
 if stored!=reply{return Err(Error::Checkpoint);}Ok(())
}
#[kani::proof_for_contract(proof_digest_frame_cut)]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn proof_digest_frame_contract(){
 let stored:[u8;32]=kani::any();let proof:[u8;57607]=kani::any();let mut log=Descriptor{calls:0,ptr:core::ptr::null(),len:0,reply:kani::any()};let _=proof_digest_frame_cut(&stored,&proof,&mut log);
}
