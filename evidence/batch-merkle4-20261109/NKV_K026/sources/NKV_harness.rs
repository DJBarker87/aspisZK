use super::*;
#[allow(non_snake_case)]
mod kmx { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../NKV_fragments.rs"));

#[derive(Clone,Copy)]
struct ParentOracle<'a> {
 phase:&'a core::cell::Cell<usize>,
 replies:[u8;3],roots:[[u8;32];3],queries:[u32;22],batch:usize,
 proof:*const u8,width:usize,j:usize,k:usize,
 post_i:&'a core::cell::Cell<u32>,post_v:&'a core::cell::Cell<u8>,
}
impl Digest32 for ParentOracle<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let phase=self.phase.get(); let tree=phase/3;
  assert!(tree<3); self.phase.set(phase+1);
  let mut reply=[0u8;32];
  if phase%3==0 {
   assert!(parts.is_empty());reply[0]=self.j as u8;reply[1]=self.k as u8;
  } else if phase%3==1 {
   assert!((parts.len())==(7),"NKV comparison source line 19");
   assert!((parts[0].as_ptr())==(self.proof),"NKV comparison source line 20");assert!((parts[0].len())==(self.width),"NKV comparison source line 20");
   #[cfg(not(NKV_copy_control))] assert!((parts[1])==(&self.roots[tree]),"NKV comparison source line 21");
   #[cfg(NKV_copy_control)] assert!(parts[1]!=&self.roots[tree],"NKV copied root negative control");
   assert!((parts[2])==(&self.batch.to_le_bytes()),"NKV comparison source line 22");assert!((parts[3])==(&tree.to_le_bytes()),"NKV comparison source line 22");
   assert!((parts[4].len())==(88),"NKV comparison source line 23");
   for i in 0..22 { assert!((&parts[4][4*i..4*i+4])==(&self.queries[i].to_le_bytes()),"NKV comparison source line 24"); }
   assert!(parts[5].len()==4);assert!(parts[6].len()==1);
   let j=self.j;let k=self.k;
   let before_i=u32::from_le_bytes(parts[5].try_into().unwrap());let before_v=parts[6][0];
   assert!((before_i)==(if tree==0 {0}else{self.post_i.get()}),"NKV comparison source line 28");
   if tree==0 { assert!(before_v==0,"NKV initial value array is zero"); } else { assert!(before_v==self.post_v.get(),"NKV value array threads previous child poststate"); }
   reply[0]=self.replies[tree];reply[1]=self.j as u8;reply[2]=self.k as u8;
  } else {
   assert!((parts.len())==(2),"NKV comparison source line 32");
   let j=self.j;let k=self.k;
   self.post_i.set(u32::from_le_bytes(parts[0].try_into().unwrap()));self.post_v.set(parts[1][0]);
  }
  reply
 }
}
fn logged_tree<H:Digest32>(proof:&[u8],queries:[u32;22],root:[u8;32],batch:usize,tree:usize,idx:&mut[u32;16],val:&mut[[u8;32];16],hash:H)->Result<(),Error> {
 let probe=hash.digest(&[]);let j=probe[0]as usize;let k=probe[1]as usize;assert!(j<16&&k<32);
 let queries_bytes=unsafe{core::slice::from_raw_parts(queries.as_ptr()as *const u8,88)};
 let reply=hash.digest(&[proof,&root,&batch.to_le_bytes(),&tree.to_le_bytes(),queries_bytes,&idx[j].to_le_bytes(),&val[j][k..k+1]]);
 *idx=kani::any();*val=kani::any();
 hash.digest(&[&idx[j].to_le_bytes(),&val[j][k..k+1]]);
 match reply[0] {0=>Ok(()),1=>Err(Error::Parse),_=>Err(Error::Merkle)}
}
#[kani::proof]
#[kani::unwind(600)]
#[kani::stub(batch_tree,logged_tree)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn values_calls() {
 let proof:[u8;57607]=kani::any();let queries:[u32;22]=kani::any();let roots:[[u8;32];3]=kani::any();let batch:usize=kani::any();kani::assume(batch<2);
 let replies:[u8;3]=kani::any();kani::assume(replies[0]<3&&replies[1]<3&&replies[2]<3);
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);
 let phase=core::cell::Cell::new(0);let post_i=core::cell::Cell::new(0);let post_v=core::cell::Cell::new(0);
 let oracle=ParentOracle{phase:&phase,replies,roots,queries,batch,proof:proof.as_ptr(),width:proof.len(),j,k,post_i:&post_i,post_v:&post_v};
 let out=batch_merkle_values(&proof,queries,roots,batch,oracle);
 let entered=if replies[0]!=0 {1}else if replies[1]!=0 {2}else{3};
 assert!((phase.get())==(3*entered),"NKV comparison source line 63");
 let code=if replies[0]!=0 {replies[0]}else if replies[1]!=0 {replies[1]}else{replies[2]};
 let exact=match code {0=>out.is_ok(),1=>matches!(out,Err(Error::Parse)),_=>matches!(out,Err(Error::Merkle))};
 #[cfg(not(NKV_invert))] assert!(exact);
 #[cfg(NKV_invert)] assert!(!exact);
}

#[kani::proof]
fn count_return(){
 let present:bool=kani::any();let value:usize=kani::any();
 let counted=if present {Some(value)}else{None};
 let out=count_return_fragment(counted);
 let exact=if present {matches!(out,Ok(v) if v==value)}else{matches!(out,Err(Error::Merkle))};
 #[cfg(not(NKV_invert))] assert!(exact);
 #[cfg(NKV_invert)] assert!(!exact);
}

#[derive(Clone,Copy)]
struct BatchOracle<'a>{calls:&'a core::cell::Cell<usize>,roots:[[u8;32];3],queries:[u32;22],batch:usize,proof:*const u8,width:usize,reply:u8}
impl Digest32 for BatchOracle<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{
 assert!(self.calls.get()==0);self.calls.set(1);
 assert!(parts.len()==6);assert!(parts[0].as_ptr()==self.proof&&parts[0].len()==self.width);
 assert!(parts[1]==&self.roots[0]);assert!(parts[2]==&self.roots[1]);
 #[cfg(not(NKV_copy_control))] assert!(parts[3]==&self.roots[2]);
 #[cfg(NKV_copy_control)] assert!(parts[3]!=&self.roots[2]);
 assert!(parts[4]==&self.batch.to_le_bytes());assert!(parts[5].len()==88);
 for i in 0..22{assert!(&parts[5][4*i..4*i+4]==&self.queries[i].to_le_bytes());}
 let mut out=[0;32];out[0]=self.reply;out
}}
fn logged_values<H:Digest32>(proof:&[u8],queries:[u32;22],roots:[[u8;32];3],batch:usize,hash:H)->Result<(),Error>{
 let query_bytes=unsafe{core::slice::from_raw_parts(queries.as_ptr()as *const u8,88)};
 let r=hash.digest(&[proof,&roots[0],&roots[1],&roots[2],&batch.to_le_bytes(),query_bytes]);
 match r[0]{0=>Ok(()),1=>Err(Error::Parse),_=>Err(Error::Merkle)}
}
fn any_k()->K{
 let words:[u32;4]=kani::any();
 K{c0:aspis_core::field::CM31{a:M31(words[0]),b:M31(words[1])},c1:aspis_core::field::CM31{a:M31(words[2]),b:M31(words[3])}}
}
fn any_e()->E{
 let words:[u32;8]=kani::any();for w in words{kani::assume(w<aspis_core::field::P)}
 E::from_limbs(words).unwrap()
}
#[kani::proof]
#[kani::unwind(600)]
#[kani::stub(batch_merkle_values,logged_values)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn batch_calls(){
 let proof:[u8;57607]=kani::any();let queries:[u32;22]=kani::any();let roots:[[u8;32];2]=kani::any();let folded:[u8;32]=kani::any();let state:[u8;32]=kani::any();
 let variant:u8=kani::any();kani::assume(variant<3);let variant=match variant{0=>Variant::S1,1=>Variant::S2,_=>Variant::D};
 let p=Prepared{variant,roots,gamma:any_e(),kappa:any_e(),alpha:[any_e(),any_e()],rho:any_k(),queries,semantic_alpha:core::array::from_fn(|_|any_k()),z:core::array::from_fn(|_|SecureCirclePoint{x:any_k(),y:any_k()}),claim:any_e(),state};
 let batch:usize=kani::any();kani::assume(batch<2);let reply:u8=kani::any();kani::assume(reply<3);let calls=core::cell::Cell::new(0);
 let oracle=BatchOracle{calls:&calls,roots:[roots[0],roots[1],folded],queries,batch,proof:proof.as_ptr(),width:proof.len(),reply};
 let out=batch_merkle(&proof,&p,&folded,batch,oracle);assert!(calls.get()==1);
 let exact=match reply{0=>out.is_ok(),1=>matches!(out,Err(Error::Parse)),_=>matches!(out,Err(Error::Merkle))};
 #[cfg(not(NKV_invert))] assert!(exact);
 #[cfg(NKV_invert)] assert!(!exact);
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<2&&k<32);assert!(p.roots[j][k]==roots[j][k]);
}

#[kani::proof]
fn prefix_size(){
 let count:usize=kani::any();kani::assume(count<=172);
 let size=prefix_size_fragment(count);assert!(size<=5504&&size<=9216);
 #[cfg(not(NKV_invert))] assert!(size==count<<5);
 #[cfg(NKV_invert)] assert!(size!=count<<5);
}
