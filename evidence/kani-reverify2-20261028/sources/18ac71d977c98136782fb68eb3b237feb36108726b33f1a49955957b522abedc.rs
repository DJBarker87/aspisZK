#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[kani::proof]
#[kani::unwind(17)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn KMZ_expand_copy_window() {
 let source:[u8;16]=kani::any();let mut dst:[u8;96]=kani::any();
 let at:usize=kani::any();kani::assume(at<=80);
 let j:usize=kani::any();kani::assume(j<96);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[at..at+16],&source);
 assert_eq!(dst[j],if at<=j && j<at+16 {source[j-at]} else {old});
}
#[kani::proof]
#[kani::unwind(17)]
fn KMZ_expand_zero_window() {
 let mut dst:[u8;96]=kani::any();let at:usize=kani::any();kani::assume(at<=80);
 let j:usize=kani::any();kani::assume(j<96);let old=dst[j];
 dst[at..at+16].fill(0);
 assert_eq!(dst[j],if at<=j && j<at+16 {0} else {old});
}

#[kani::proof]
fn KMZ_expand_metadata() {
 let mut backing:[u8;96]=kani::any();let slot:usize=kani::any();kani::assume(slot<3);
 let at=32*slot;let end:usize=kani::any();kani::assume(at+32<=end && end<=96);
 let base=backing.as_mut_ptr();let window=&mut backing[..end][at..at+32];
 assert!(core::ptr::eq(window.as_ptr(),base.wrapping_add(at)));
 assert_eq!(window.len(),32);assert_eq!(16usize%16,0);assert_eq!(window.len(),2*16);
 assert!(core::ptr::eq(backing.as_ptr(),base));
}

#[path="KMY_field.rs"] mod field;
use field::{WideExact as E,QM31 as K,CM31,M31};
fn any_e()->E {let raw:[u32;8]=kani::any();for x in raw{kani::assume(x<0x7fff_ffff);}E::from_limbs(raw).unwrap()}
#[kani::proof] #[kani::unwind(33)]
fn KMZ_wide_one_window() {
 let e=any_e();let raw=e.to_limbs();let src=e.to_le_bytes();
 let mut dst:[u8;64]=kani::any();let pos:usize=kani::any();kani::assume(pos<=32);
 let j:usize=kani::any();kani::assume(j<64);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+32],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+32{let b=j-pos;raw[b/4].to_le_bytes()[b%4]}else{old});
}
#[kani::proof] #[kani::unwind(5)]
fn KMZ_limb_window() {
 let raw:u32=kani::any();let src=raw.to_le_bytes();let mut dst:[u8;32]=kani::any();
 let pos:usize=kani::any();kani::assume(pos<=28);let j:usize=kani::any();kani::assume(j<32);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+4],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+4{(raw>>(8*(j-pos)))as u8}else{old});
}

#[derive(Debug,PartialEq)]enum Error {Parse}
#[derive(Debug,PartialEq)]enum Variant {S2}
struct View<'a>{variant:Variant,semantic:&'a[u8],y1:&'a[u8],inactive:E,round0:&'a[u8],folded_root:Option<&'a[u8;32]>,round1:&'a[u8],final_message:&'a[u8],query_bytes:&'a[u8]}
mod verifier {pub const SEMANTIC_BYTES:usize=12903+29*32;}
mod compact {
pub const HEADER: usize = 16;
pub const QUERIES: usize = 22;
pub const LOGICAL_SEMANTIC: usize = crate::verifier::SEMANTIC_BYTES;
pub const SEMANTIC_COMPACT_VALUES: usize = 1 + 10 * 28 + (87 + 29) + 29;
pub const COMPACT_SEMANTIC: usize = LOGICAL_SEMANTIC - 16 * SEMANTIC_COMPACT_VALUES;
pub const COMPACT_Y1: usize = 29 * 16;
pub const OFF_SEMANTIC: usize = HEADER;
pub const OFF_Y1: usize = OFF_SEMANTIC + COMPACT_SEMANTIC;
pub const OFF_INACTIVE: usize = OFF_Y1 + COMPACT_Y1;
pub const OFF_ROUND0: usize = OFF_INACTIVE + 32;
pub const OFF_FOLDED_ROOT: usize = OFF_ROUND0 + 224;
pub const OFF_ROUND1: usize = OFF_FOLDED_ROOT + 32;
pub const OFF_FINAL: usize = OFF_ROUND1 + 224;
pub const FINAL_LEN: usize = 64;
pub const OFF_OPENINGS: usize = OFF_FINAL + FINAL_LEN * 32;
pub const OPENING: usize = 480 + 128 + 32 + 32 + 128 + 32;
pub const OFF_NODES: usize = OFF_OPENINGS + QUERIES * OPENING;
pub const MAX_NODES: usize = 2 * (146 + 172) + (128 + 150);
pub const FIXED: usize = OFF_NODES;
pub const MAX_PROOF: usize = FIXED + 32 * MAX_NODES;
pub const PROOF_BYTES: usize = MAX_PROOF;
}
fn wide_view<'a>(proof: &'a [u8], semantic: &'a [u8], y1: &'a [u8]) -> Result<View<'a>, Error> {
    Ok(View {
        variant: Variant::S2,
        semantic,
        y1,
        inactive: E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: Some(proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap()),
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    })
}

#[kani::proof] #[kani::unwind(33)]
fn KMZ_view_layout_after_window(){
 let mut proof=[0u8;57607];let b:[u8;32]=kani::any();
 // Split at the completed copy; indexed writes establish the input relation.
 for j in 0..32 {proof[compact::OFF_INACTIVE+j]=b[j];}
 let semantic=[0u8;13831];let y1=[0u8;928];
 let actual=wide_view(&proof,&semantic,&y1);let inactive=E::from_le_bytes(&b);
 match (actual,inactive){
 (Err(e),None)=>assert_eq!(e,Error::Parse),
 (Ok(v),Some(x))=>{
 assert_eq!(v.inactive,x);assert_eq!(v.variant,Variant::S2);
 assert!(core::ptr::eq(v.semantic.as_ptr(),semantic.as_ptr()));assert_eq!(v.semantic.len(),semantic.len());
 assert!(core::ptr::eq(v.y1.as_ptr(),y1.as_ptr()));assert_eq!(v.y1.len(),y1.len());
 assert!(core::ptr::eq(v.round0.as_ptr(),proof[compact::OFF_ROUND0..].as_ptr()));assert_eq!(v.round0.len(),224);
 assert!(core::ptr::eq(v.folded_root.unwrap().as_ptr(),proof[compact::OFF_FOLDED_ROOT..].as_ptr()));
 assert!(core::ptr::eq(v.round1.as_ptr(),proof[compact::OFF_ROUND1..].as_ptr()));assert_eq!(v.round1.len(),224);
 assert!(core::ptr::eq(v.final_message.as_ptr(),proof[compact::OFF_FINAL..].as_ptr()));assert_eq!(v.final_message.len(),2048);
 assert_eq!(v.query_bytes.len(),0);
 },_=>assert!(false)
 }
}
#[kani::proof] #[kani::unwind(33)]
fn KMZ_view_copy_window(){
 let source:[u8;32]=kani::any();let mut dst:[u8;57607]=kani::any();
 let pos:usize=kani::any();kani::assume(pos<=57575);let j:usize=kani::any();kani::assume(j<57607);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+32],&source);
 assert_eq!(dst[j],if pos<=j && j<pos+32{source[j-pos]}else{old});
}

fn byte_window<const N:usize>() {
 let src:[u8;N]=kani::any();let mut dst:[u8;1768]=kani::any();
 let pos:usize=kani::any();kani::assume(pos<=1768-N);
 let j:usize=kani::any();kani::assume(j<1768);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+N],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+N{src[j-pos]}else{old});
}
#[kani::proof] #[kani::unwind(17)] fn KMZ_checkpoint_window16(){byte_window::<16>();}
#[kani::proof] #[kani::unwind(33)] fn KMZ_checkpoint_window32(){byte_window::<32>();}
#[kani::proof] #[kani::unwind(5)] fn KMZ_checkpoint_window4(){byte_window::<4>();}
#[kani::proof] #[kani::unwind(67)]
fn KMZ_weights_copy_window(){
 let raw:[[u32;4];64]=kani::any();
 let src=raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}});
 let mut dst:[K;66]=core::array::from_fn(|_|{let r:[u32;4]=kani::any();K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}});
 let pos:usize=kani::any();kani::assume(pos<=2);let j:usize=kani::any();kani::assume(j<66);
 let old=dst[j];KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+64],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+64{src[j-pos]}else{old});
}
#[kani::proof] #[kani::unwind(17)]
fn KMZ_scalar_one_window(){
 let raw:[u32;4]=kani::any();let k=K{c0:CM31{a:M31(raw[0]),b:M31(raw[1])},c1:CM31{a:M31(raw[2]),b:M31(raw[3])}};
 let mut src=[0u8;16];k.write_le_bytes(&mut src);
 let mut dst:[u8;48]=kani::any();let pos:usize=kani::any();kani::assume(pos<=32);
 let j:usize=kani::any();kani::assume(j<48);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+16],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+16{let b=j-pos;raw[b/4].to_le_bytes()[b%4]}else{old});
}

#[kani::proof] #[kani::unwind(33)]
fn KMZ_local_window32(){
 let src:[u8;32]=kani::any();let mut dst:[u8;64]=kani::any();
 let pos:usize=kani::any();kani::assume(pos<=32);let j:usize=kani::any();kani::assume(j<64);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+32],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+32{src[j-pos]}else{old});
}
#[kani::proof] #[kani::unwind(33)]
fn KMZ_view_accept_layout(){
 let e=any_e();let b=e.to_le_bytes();let mut proof=[0u8;57607];
 for j in 0..32 {proof[compact::OFF_INACTIVE+j]=b[j];}
 let semantic=[0u8;13831];let y1=[0u8;928];let v=wide_view(&proof,&semantic,&y1).unwrap();
 assert_eq!(v.inactive,e);assert_eq!(v.variant,Variant::S2);
 assert!(core::ptr::eq(v.semantic.as_ptr(),semantic.as_ptr()));assert_eq!(v.semantic.len(),semantic.len());
 assert!(core::ptr::eq(v.y1.as_ptr(),y1.as_ptr()));assert_eq!(v.y1.len(),y1.len());
 assert!(core::ptr::eq(v.round0.as_ptr(),proof[compact::OFF_ROUND0..].as_ptr()));assert_eq!(v.round0.len(),224);
 assert!(core::ptr::eq(v.folded_root.unwrap().as_ptr(),proof[compact::OFF_FOLDED_ROOT..].as_ptr()));
 assert!(core::ptr::eq(v.round1.as_ptr(),proof[compact::OFF_ROUND1..].as_ptr()));assert_eq!(v.round1.len(),224);
 assert!(core::ptr::eq(v.final_message.as_ptr(),proof[compact::OFF_FINAL..].as_ptr()));assert_eq!(v.final_message.len(),2048);
 assert_eq!(v.query_bytes.len(),0);
}
fn view_reject<const BAD:usize>(){
 let mut raw:[u32;8]=kani::any();kani::assume(raw[BAD]>=0x7fff_ffff);
 let mut proof=[0u8;57607];for limb in 0..8{for byte in 0..4{proof[compact::OFF_INACTIVE+4*limb+byte]=raw[limb].to_le_bytes()[byte];}}
 assert!(matches!(wide_view(&proof,&[],&[]),Err(Error::Parse)));
}
#[kani::proof] #[kani::unwind(9)] fn KMZ_view_reject0(){view_reject::<0>();}
#[kani::proof] #[kani::unwind(9)] fn KMZ_view_reject1(){view_reject::<1>();}
#[kani::proof] #[kani::unwind(9)] fn KMZ_view_reject2(){view_reject::<2>();}
#[kani::proof] #[kani::unwind(9)] fn KMZ_view_reject3(){view_reject::<3>();}
#[kani::proof] #[kani::unwind(9)] fn KMZ_view_reject4(){view_reject::<4>();}
#[kani::proof] #[kani::unwind(9)] fn KMZ_view_reject5(){view_reject::<5>();}
#[kani::proof] #[kani::unwind(9)] fn KMZ_view_reject6(){view_reject::<6>();}
#[kani::proof] #[kani::unwind(9)] fn KMZ_view_reject7(){view_reject::<7>();}
#[kani::proof] #[kani::unwind(193)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_wide_append_one(){
 let initial:[u8;160]=kani::any();let slot:usize=kani::any();kani::assume(slot<6);let len=32*slot;
 let e=any_e();let raw=e.to_limbs();let encoded=e.to_le_bytes();
 let mut out=KMX_stubs::KMX_to_vec(&initial[..len]);
 KMX_stubs::KMX_extend_from_slice(&mut out,&encoded);
 assert_eq!(out.len(),len+32);let j:usize=kani::any();kani::assume(j<out.len());
 assert_eq!(out[j],if j<len{initial[j]}else{let b=j-len;raw[b/4].to_le_bytes()[b%4]});
}
#[kani::proof] #[kani::unwind(33)]
fn KMZ_parse_accept(){
 let e=any_e();let encoded=e.to_le_bytes();let mut local=[0u8;32];
 KMX_stubs::KMX_copy_from_slice(&mut local,&encoded);
 assert_eq!(E::from_le_bytes(&local),Some(e));
}
#[kani::proof] #[kani::unwind(9)]
fn KMZ_view_metadata_zero(){
 let proof=[0u8;57607];let semantic=[0u8;13831];let y1=[0u8;928];
 let v=wide_view(&proof,&semantic,&y1).unwrap();
 assert_eq!(v.variant,Variant::S2);assert_eq!(v.inactive,E::ZERO);
 assert!(core::ptr::eq(v.semantic.as_ptr(),semantic.as_ptr()));assert_eq!(v.semantic.len(),semantic.len());
 assert!(core::ptr::eq(v.y1.as_ptr(),y1.as_ptr()));assert_eq!(v.y1.len(),y1.len());
 assert!(core::ptr::eq(v.round0.as_ptr(),proof[compact::OFF_ROUND0..].as_ptr()));assert_eq!(v.round0.len(),224);
 assert!(core::ptr::eq(v.folded_root.unwrap().as_ptr(),proof[compact::OFF_FOLDED_ROOT..].as_ptr()));
 assert!(core::ptr::eq(v.round1.as_ptr(),proof[compact::OFF_ROUND1..].as_ptr()));assert_eq!(v.round1.len(),224);
 assert!(core::ptr::eq(v.final_message.as_ptr(),proof[compact::OFF_FINAL..].as_ptr()));assert_eq!(v.final_message.len(),2048);
 assert_eq!(v.query_bytes.len(),0);
}

trait Digest32 {fn digest(&self,parts:&[&[u8]])->[u8;32];}
#[derive(Clone,Copy)] pub(crate) struct Ordered<'a>{pub(crate) count:&'a core::cell::Cell<usize>,pub(crate) proof:&'a[u8],pub(crate) public:&'a[u8],pub(crate) answers:[[u8;32];3]}
impl Digest32 for Ordered<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{let i=self.count.get();assert!(i<3);match i{0=>{assert_eq!(parts.len(),1);assert_eq!(parts[0],self.proof);},1=>{assert_eq!(parts.len(),1);assert_eq!(parts[0],self.public);},2=>{assert_eq!(parts.len(),2);assert_eq!(parts[0],b"UNPROVED:R1:checkpoint");assert_eq!(parts[1].len(),1736);},_=>unreachable!()};self.count.set(i+1);self.answers[i]}}
#[derive(Clone,Copy)]struct Checksum<'a>{count:&'a core::cell::Cell<usize>,prefix:&'a[u8],index:usize,answer:[u8;32]}
impl Digest32 for Checksum<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{assert_eq!(self.count.get(),2);assert_eq!(parts.len(),2);assert_eq!(parts[0].len(),22);assert_eq!(parts[0],b"UNPROVED:R1:checkpoint");assert_eq!(parts[1].len(),1736);assert_eq!(parts[1][self.index],self.prefix[self.index]);self.count.set(3);self.answer}}
#[derive(Clone,Copy)]
struct JoinedOracle<'a>{count:&'a core::cell::Cell<usize>,proof:&'a[u8],public:&'a[u8],body:&'a[u8;1736],selected:usize,answers:[[u8;32];3]}
impl Digest32 for JoinedOracle<'_>{
 fn digest(&self,parts:&[&[u8]])->[u8;32]{
  let n=self.count.get();assert!(n<3);
  match n {
   0=>{assert_eq!(parts.len(),1);assert_eq!(parts[0].len(),self.proof.len());assert_eq!(parts[0].as_ptr(),self.proof.as_ptr());}
   1=>{assert_eq!(parts.len(),1);assert_eq!(parts[0].len(),self.public.len());assert_eq!(parts[0].as_ptr(),self.public.as_ptr());}
   _=>{assert_eq!(parts.len(),2);assert_eq!(parts[0],b"UNPROVED:R1:checkpoint");assert_eq!(parts[1].len(),1736);assert_eq!(parts[1][self.selected],joined_byte(self.body,&self.answers,self.selected));}
  }
  self.count.set(n+1);self.answers[n]
 }
}
fn joined_byte(body:&[u8;1736],answers:&[[u8;32];3],at:usize)->u8 {
 if (16..48).contains(&at){answers[0][at-16]}
 else if (48..80).contains(&at){answers[1][at-48]}
 else if at<1736{body[at]}else{answers[2][at-1736]}
}

#[kani::proof] #[kani::unwind(33)]
fn KMZ_digest_prefix_oracle(){
 let proof:[u8;3]=kani::any();let public:[u8;5]=kani::any();let answers:[[u8;32];3]=kani::any();
 let count=core::cell::Cell::new(0);let hash=Ordered{count:&count,proof:&proof,public:&public,answers};
 let hp=hash.digest(&[&proof]);let hu=hash.digest(&[&public]);assert_eq!(count.get(),2);
 let j:usize=kani::any();kani::assume(j<32);assert_eq!(hp[j],answers[0][j]);assert_eq!(hu[j],answers[1][j]);
}
#[kani::proof] #[kani::unwind(33)]
fn KMZ_checksum_oracle(){
 let prefix:[u8;1736]=kani::any();let answer:[u8;32]=kani::any();let index:usize=kani::any();kani::assume(index<1736);
 let count=core::cell::Cell::new(2);let hash=Checksum{count:&count,prefix:&prefix,index,answer};
 let sum=hash.digest(&[b"UNPROVED:R1:checkpoint",&prefix]);assert_eq!(count.get(),3);
 let j:usize=kani::any();kani::assume(j<32);assert_eq!(sum[j],answer[j]);
}
fn joined_oracle<const PROOF:usize,const PUBLIC:usize>(){
 let proof=[0u8;PROOF];let public=[0u8;PUBLIC];let body:[u8;1736]=kani::any();let answers:[[u8;32];3]=kani::any();
 let selected:usize=kani::any();kani::assume(selected<1736);let count=core::cell::Cell::new(0);
 let hash=JoinedOracle{count:&count,proof:&proof,public:&public,body:&body,selected,answers};
 let hp=hash.digest(&[&proof]);let hu=hash.digest(&[&public]);
 let mut completed=body;
 // This is the pointwise relation proved for every selected byte by joined_digest.
 completed[selected]=joined_byte(&body,&answers,selected);
 let sum=hash.digest(&[b"UNPROVED:R1:checkpoint",&completed]);assert_eq!(count.get(),3);
 let j:usize=kani::any();kani::assume(j<32);assert_eq!(hp[j],answers[0][j]);assert_eq!(hu[j],answers[1][j]);assert_eq!(sum[j],answers[2][j]);
}
#[kani::proof] #[kani::unwind(33)] fn KMZ_joined_oracle_small(){joined_oracle::<3,5>();}
#[kani::proof] #[kani::unwind(33)] fn KMZ_joined_oracle_physical(){joined_oracle::<57607,1880>();}
#[kani::proof] #[kani::unwind(9)]
fn KMZ_local_parse_reject(){
 let raw:[u32;8]=kani::any();let bad:usize=kani::any();kani::assume(bad<8);kani::assume(raw[bad]>=0x7fff_ffff);
 let mut bytes=[0u8;32];for limb in 0..8{for byte in 0..4{bytes[4*limb+byte]=raw[limb].to_le_bytes()[byte];}}
 assert!(E::from_le_bytes(&bytes).is_none());
}
#[kani::proof] #[kani::unwind(67)]
fn KMZ_weights_copy_limb(){
 let raw:[[u32;4];64]=kani::any();
 let src=raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}});
 let mut dst:[K;66]=core::array::from_fn(|_|{let r:[u32;4]=kani::any();K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}});
 let pos:usize=kani::any();kani::assume(pos<=2);let j:usize=kani::any();kani::assume(j<66);
 let limb:usize=kani::any();kani::assume(limb<4);
 let words=|x:K|[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0];let old=words(dst[j])[limb];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+64],&src);
 assert_eq!(words(dst[j])[limb],if pos<=j && j<pos+64{raw[j-pos][limb]}else{old});
}
#[kani::proof] #[kani::unwind(65)]
fn KMZ_weights_iterator_after_copy(){
 let raw:[[u32;4];64]=kani::any();let words=|x:K|[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0];
 let src=raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}});
 let i:usize=kani::any();kani::assume(i<=64);let mut iter=src[i..].iter();let item=iter.next();
 assert_eq!(item.is_none(),i==64);
 if let Some(&x)=item{let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(words(x)[limb],raw[i][limb]);}
 assert_eq!(iter.as_slice().len(),if i==64{0}else{63-i});
 if i<63{let j:usize=kani::any();kani::assume(j<63-i);let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(words(iter.as_slice()[j])[limb],raw[i+1+j][limb]);}
 assert_eq!(src.len(),64);
}
fn wide_append_stage<const LEN:usize,const CAP:usize>(){
 let initial:[u8;160]=kani::any();let e=any_e();let raw=e.to_limbs();let encoded=e.to_le_bytes();
 let mut out=alloc::vec::Vec::with_capacity(CAP);
 KMX_stubs::KMX_extend_from_slice(&mut out,&initial[..LEN]);
 KMX_stubs::KMX_extend_from_slice(&mut out,&encoded);
 assert_eq!(out.len(),LEN+32);let j:usize=kani::any();kani::assume(j<out.len());
 assert_eq!(out[j],if j<LEN{initial[j]}else{let b=j-LEN;raw[b/4].to_le_bytes()[b%4]});
}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_wide_stage0(){wide_append_stage::<0,0>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_wide_stage1(){wide_append_stage::<32,32>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_wide_stage2(){wide_append_stage::<64,64>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_wide_stage3(){wide_append_stage::<96,128>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_wide_stage4(){wide_append_stage::<128,128>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_wide_stage5(){wide_append_stage::<160,256>();}

fn scalar_append_stage<const LEN:usize,const CAP:usize>(){
 let initial:[u8;208]=kani::any();let raw:[u32;4]=kani::any();
 let k=K{c0:CM31{a:M31(raw[0]),b:M31(raw[1])},c1:CM31{a:M31(raw[2]),b:M31(raw[3])}};
 let mut encoded=[0u8;16];k.write_le_bytes(&mut encoded);
 let mut out=alloc::vec::Vec::with_capacity(CAP);
 KMX_stubs::KMX_extend_from_slice(&mut out,&initial[..LEN]);
 KMX_stubs::KMX_extend_from_slice(&mut out,&encoded);
 assert_eq!(out.len(),LEN+16);let j:usize=kani::any();kani::assume(j<out.len());
 assert_eq!(out[j],if j<LEN{initial[j]}else{let b=j-LEN;raw[b/4].to_le_bytes()[b%4]});
}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage0(){scalar_append_stage::<0,0>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage1(){scalar_append_stage::<16,16>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage2(){scalar_append_stage::<32,32>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage3(){scalar_append_stage::<48,64>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage4(){scalar_append_stage::<64,64>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage5(){scalar_append_stage::<80,128>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage6(){scalar_append_stage::<96,128>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage7(){scalar_append_stage::<112,128>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage8(){scalar_append_stage::<128,128>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage9(){scalar_append_stage::<144,256>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage10(){scalar_append_stage::<160,256>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage11(){scalar_append_stage::<176,256>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage12(){scalar_append_stage::<192,256>();}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_scalar_stage13(){scalar_append_stage::<208,256>();}
#[kani::proof] #[kani::unwind(65)]
fn KMZ_weights_copy_inside_zero_offset(){
 let raw:[[u32;4];64]=kani::any();let src=raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}});
 let mut dst=[K::ZERO;64];KMX_stubs::KMX_copy_from_slice(&mut dst,&src);
 let j:usize=kani::any();kani::assume(j<64);let limb:usize=kani::any();kani::assume(limb<4);
 let x=dst[j];let words=[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0];assert_eq!(words[limb],raw[j][limb]);
}
#[kani::proof] #[kani::unwind(9)]
fn KMZ_parse_arbitrary_bytes(){
 let bytes:[u8;32]=kani::any();let mut raw=[0u32;8];
 for i in 0..8{raw[i]=u32::from_le_bytes([bytes[4*i],bytes[4*i+1],bytes[4*i+2],bytes[4*i+3]]);}
 let parsed=E::from_le_bytes(&bytes);let canonical=raw.iter().all(|&x|x<0x7fff_ffff);
 assert_eq!(parsed.is_some(),canonical);
 if let Some(e)=parsed{let i:usize=kani::any();kani::assume(i<8);assert_eq!(e.to_limbs()[i],raw[i]);}
}

fn wide_view_decoder_cut<'a,F:Fn(&[u8])->Option<E>>(proof: &'a [u8], semantic: &'a [u8], y1: &'a [u8],decode:F) -> Result<View<'a>, Error> {
    Ok(View {
        variant: Variant::S2,
        semantic,
        y1,
        inactive: decode(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: Some(proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap()),
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    })
}

#[kani::proof] #[kani::unwind(9)]
fn KMZ_view_decoder_cut(){
 let e=any_e();let accepted:bool=kani::any();let parsed=if accepted{Some(e)}else{None};
 let proof=[0u8;57607];let semantic=[0u8;13831];let y1=[0u8;928];
 let result=wide_view_decoder_cut(&proof,&semantic,&y1,|input|{
 assert_eq!(input.len(),32);assert_eq!(input.as_ptr(),proof[compact::OFF_INACTIVE..].as_ptr());parsed});
 match(result,parsed){
 (Err(err),None)=>assert_eq!(err,Error::Parse),
 (Ok(v),Some(expected))=>{
 assert_eq!(v.inactive,expected);assert_eq!(v.variant,Variant::S2);
 assert!(core::ptr::eq(v.semantic.as_ptr(),semantic.as_ptr()));assert_eq!(v.semantic.len(),semantic.len());
 assert!(core::ptr::eq(v.y1.as_ptr(),y1.as_ptr()));assert_eq!(v.y1.len(),y1.len());
 assert!(core::ptr::eq(v.round0.as_ptr(),proof[compact::OFF_ROUND0..].as_ptr()));assert_eq!(v.round0.len(),224);
 assert!(core::ptr::eq(v.folded_root.unwrap().as_ptr(),proof[compact::OFF_FOLDED_ROOT..].as_ptr()));
 assert!(core::ptr::eq(v.round1.as_ptr(),proof[compact::OFF_ROUND1..].as_ptr()));assert_eq!(v.round1.len(),224);
 assert!(core::ptr::eq(v.final_message.as_ptr(),proof[compact::OFF_FINAL..].as_ptr()));assert_eq!(v.final_message.len(),2048);
 assert_eq!(v.query_bytes.len(),0);
 },_=>assert!(false)
 }
}

#[kani::proof] #[kani::unwind(65)]
fn KMZ_iterator_empty(){
 let raw:[[u32;4];64]=kani::any();let src=raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}});
 let mut iter=src[64..].iter();let item=iter.next();
 assert!(item.is_none());assert_eq!(iter.as_slice().len(),0);
}

#[kani::proof] #[kani::unwind(65)]
fn KMZ_iterator_last(){
 let raw:[[u32;4];64]=kani::any();let src=raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}});
 let mut iter=src[63..].iter();let item=iter.next();
 let x=*item.unwrap();let limb:usize=kani::any();kani::assume(limb<4);
 let words=[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0];assert_eq!(words[limb],raw[63][limb]);assert_eq!(iter.as_slice().len(),0);
}

#[kani::proof] #[kani::unwind(65)]
fn KMZ_iterator_remaining(){
 let raw:[[u32;4];64]=kani::any();let src=raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}});
 let i:usize=kani::any();kani::assume(i<63);let mut iter=src[i..].iter();let _=iter.next();
 assert_eq!(iter.as_slice().len(),63-i);let j:usize=kani::any();kani::assume(j<63-i);let limb:usize=kani::any();kani::assume(limb<4);
 let x=iter.as_slice()[j];let words=[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0];assert_eq!(words[limb],raw[i+1+j][limb]);
}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_capacity32(){
 let source:[u8;32]=kani::any();let mut out=alloc::vec::Vec::new();
 let expected=[33usize,64,128,128,256,256];
 for i in 0..6{KMX_stubs::KMX_extend_from_slice(&mut out,&source);assert_eq!(out.len(),32*(i+1));assert_eq!(out.capacity(),expected[i]);}
}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_capacity16(){
 let source:[u8;16]=kani::any();let mut out=alloc::vec::Vec::new();
 let expected=[16usize,32,64,64,128,128,128,128,256,256,256,256,256,256];
 for i in 0..14{KMX_stubs::KMX_extend_from_slice(&mut out,&source);assert_eq!(out.len(),16*(i+1));assert_eq!(out.capacity(),expected[i]);}
}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_capacity_schedules_selected(){KMZ_capacity32();KMZ_capacity16();}
