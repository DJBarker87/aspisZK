use super::{frozen as f,reference as r};
use aspis_core::{Digest32,field::{M31,QM31}};
#[derive(Clone,Copy)] struct Oracle;
static mut ANSWER:[u8;32]=[0;32];
static mut EVENT:u8=0;
static mut COORD:usize=0;
static mut CALLS:usize=0;
impl Digest32 for Oracle {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),1);
  assert_eq!(parts[1].len(),32);assert_eq!(parts[2].len(),32);
  unsafe {CALLS+=1;EVENT=if COORD==0 {parts[0][0]}else if COORD<33 {parts[1][COORD-1]}else{parts[2][COORD-33]}; ANSWER}
 }
}
// Arbitrary observation coordinates prove extensional equality without a
// 512-byte memcmp unwind or 512 separately expanded postconditions.
fn same_buffers(idx:&[u32;16],val:&[[u8;32];16],s:&r::Scratch) {
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16 && k<32);
 assert_eq!(idx[j],s.idx[j]);assert_eq!(val[j][k],s.val[j][k]);
}
fn group_at(case:u8,i:usize) {
 let s=r::Scratch{idx:kani::any(),val:kani::any(),n:kani::any(),at:kani::any()};
 let w:usize=kani::any();let nodes:[u8;64]=kani::any();let length:usize=kani::any();
 kani::assume(s.n>0 && s.n<=16 && i<s.n && w<=i && length<=64 && s.at<=length);
 let paired=i+1<s.n && s.idx[i+1]==s.idx[i]^1;
 if case==0 {kani::assume(paired);} else {kani::assume(!paired);kani::assume((length-s.at>=32)==(case==1));}
 let mut idx=s.idx;let mut val=s.val;let mut at=s.at;let mut j=i;let mut out=w;
 let coordinate:usize=kani::any();kani::assume(coordinate<65);
 unsafe {ANSWER=kani::any();COORD=coordinate;EVENT=0;CALLS=0;}
 let success=f::multiproof::binary_group(Oracle,&mut idx,&mut val,s.n,&nodes[..length],&mut at,&mut out,&mut j);
 let (event,calls)=unsafe{(EVENT,CALLS)};
 unsafe {EVENT=0;CALLS=0;}
 match r::binary_step(Oracle,s,&nodes[..length],i,w) {
  r::Row::Stop(next)=>{assert!(!success);same_buffers(&next.idx,&next.val,&s);assert_eq!((next.n,next.at),(s.n,s.at));same_buffers(&idx,&val,&s);assert_eq!((at,j,out),(s.at,i,w));},
  r::Row::Next(next,next_i,next_w)=>{assert!(success);same_buffers(&idx,&val,&next);assert_eq!((at,j,out),(next.at,next_i,next_w));assert_eq!(next.n,s.n);}
 }
 unsafe{assert_eq!(EVENT,event);assert_eq!(CALLS,calls);}
}
fn group(case:u8){group_at(case,kani::any());}
#[kani::proof] #[kani::unwind(34)] fn binary_occupied_group(){group(0);}
#[kani::proof] #[kani::stub_verified(r::read32)] #[kani::unwind(34)] fn binary_sibling_group(){group(1);}
#[kani::proof] #[kani::unwind(34)] fn binary_short_group(){group(2);}

#[kani::proof] #[kani::unwind(34)] fn leaf_batch_step(){
 let s=r::Scratch{idx:kani::any(),val:kani::any(),n:kani::any(),at:kani::any()};
 kani::assume(s.n<16);
 let index:u32=kani::any();let leaf:[u8;32]=kani::any();
 let (mut idx,mut val,mut n)=(s.idx,s.val,s.n);
 let success=f::batch::leaf_insert(&mut idx,&mut val,&mut n,index,leaf);
 match r::leaf_step(s,index,leaf) {
  None=>{assert!(!success);same_buffers(&idx,&val,&s);assert_eq!(n,s.n);},
  Some(next)=>{assert!(success);same_buffers(&idx,&val,&next);assert_eq!(n,next.n);assert_eq!(next.at,s.at);}
 }
}
#[kani::proof] #[kani::unwind(34)] fn compact_expand_value(){
 let c:[u8;16]=kani::any();let mut out:[u8;32]=kani::any();
 assert_eq!(f::compact::expand_values(&c,&mut out),Ok(()));assert_eq!(out,r::expand_chunk(c));
}
#[kani::proof] #[kani::unwind(18)] fn compact_strict_field(){
 let c:[u8;16]=kani::any();assert_eq!(f::compact::check_values(&c).is_ok(),r::canonical_qm(c));
}
#[kani::proof] #[kani::unwind(34)] fn compact_short_suffix(){
 let c:[u8;31]=kani::any();let n:usize=kani::any();kani::assume(n<=31);
 assert_eq!(f::compact::check_values(&c[..n]).is_ok(),r::check_values(&c[..n]));
}
#[kani::proof] fn semantic_row_shape(){
 let row:u8=kani::any();assert_eq!(f::r1_wire::row_shape(row),r::row_shape(row));
}
#[kani::proof] #[kani::unwind(29)] fn semantic_offsets(){
 assert_eq!(r::semantic_offsets(0,32,32),Some((7015,13831)));
}
// Each reached parser section is represented at an arbitrary value ordinal.
// These certificates cover the decoder predicate, not the surrounding caller.
#[kani::proof] fn parser_c1_m31_field(){
 let b:[u8;4]=kani::any();assert_eq!(M31::from_le_bytes(b).is_some(),r::canonical_word(b));
 let slot:usize=kani::any();let limb:usize=kani::any();kani::assume(slot<4 && limb<26);
 assert!(slot*120+limb*4+4<=480);
}
#[kani::proof] fn parser_c1_k_field(){
 let b:[u8;16]=kani::any();assert_eq!(QM31::from_le_bytes(&b).is_some(),r::canonical_qm(b));
 let slot:usize=kani::any();kani::assume(slot<4);assert!(slot*120+104+16<=480);
}
#[kani::proof] fn parser_c2_k_field(){
 let b:[u8;16]=kani::any();assert_eq!(QM31::from_le_bytes(&b).is_some(),r::canonical_qm(b));
 let slot:usize=kani::any();let limb:usize=kani::any();kani::assume(slot<4 && limb<2);
 assert!(480+slot*32+limb*16+16<=608);
}
#[kani::proof] fn parser_wide_field(){
 let b:[u8;32]=kani::any();
 let lhs=aspis_core::field::WideExact::from_le_bytes(&b).is_some();
 let low:[u8;16]=b[..16].try_into().unwrap();let high:[u8;16]=b[16..].try_into().unwrap();
 assert_eq!(lhs,r::canonical_qm(low)&&r::canonical_qm(high));
}
#[kani::proof] #[kani::unwind(34)] fn batch_sorted_key_step(){
 let queries:[u32;22]=kani::any();let batch:bool=kani::any();let tree:usize=kani::any();kani::assume(tree<3);
 let (lo,n)=if batch {(10,12)}else{(0,10)};
 let keys=f::batch::batch_keys(&queries,lo,n,tree);
 let j:usize=kani::any();kani::assume(j<n);
 let index=if tree==2 {queries[lo+j]/4}else{queries[lo+j]};
 assert_eq!(keys[j]>>8,u64::from(index));assert_eq!(keys[j]&255,j as u64);
}

#[kani::proof_for_contract(r::read32)] #[kani::unwind(34)]
fn read32_contract(){let bytes:[u8;32]=kani::any();r::read32(&bytes);}

#[derive(Clone,Copy)] struct LeafOracle;
static mut LEAF_COORD:usize=0;
static mut LEAF_TREE:usize=0;
impl Digest32 for LeafOracle {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  unsafe {
   let width=if LEAF_TREE==0 {480}else{128};
   assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),2);
   assert_eq!(parts[1].len(),width);assert_eq!(parts[2].len(),32);
   CALLS+=1;
   EVENT=if LEAF_COORD<2 {parts[0][LEAF_COORD]}else if LEAF_COORD<2+width {parts[1][LEAF_COORD-2]}else{parts[2][LEAF_COORD-2-width]};
   ANSWER
  }
 }
}
#[kani::proof] #[kani::unwind(34)] fn batch_leaf_grammar(){
 let bytes:[u8;832]=kani::any();let tree:usize=kani::any();kani::assume(tree<3);
 let (tag,start,width,salt)=if tree==0 {(0x71,0,480,608)}else if tree==1 {(0xf1,480,128,640)}else{(0x72,672,128,800)};
 let coordinate:usize=kani::any();kani::assume(coordinate<2+width+32);
 unsafe {LEAF_TREE=tree;LEAF_COORD=coordinate;ANSWER=kani::any();CALLS=0;EVENT=0;}
 let out=f::batch::batch_leaf(LeafOracle,tree,&bytes);
 let expected=if coordinate==0 {0x10}else if coordinate==1 {tag}else if coordinate<2+width {bytes[start+coordinate-2]}else{bytes[salt+coordinate-2-width]};
 let j:usize=kani::any();kani::assume(j<32);
 unsafe{assert_eq!(EVENT,expected);assert_eq!(CALLS,1);assert_eq!(out[j],ANSWER[j]);}
}
#[kani::proof] #[kani::unwind(10)] fn padding_word_exact(){
 let word:[u8;8]=kani::any();
 let source=u64::from_le_bytes(word)!=0;
 let reference=word.iter().any(|&b|b!=0);
 assert_eq!(source,reference);
}
#[kani::proof] #[kani::unwind(18)] fn node_count_binary_group(){
 let mut level:[u32;16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();
 kani::assume(n>0 && n<=16 && i<n && w<=i);
 kani::assume(f::multiproof::well_formed(&level[..n]));
 let index=level[i];
 let paired=i+1<n && index%2==0 && level[i+1]==index+1;
 let (j,next_w,contribution)=f::multiproof::count_group(&mut level,n,i,w);
 assert_eq!(j,if paired {i+2}else{i+1});
 assert_eq!(next_w,w+1);assert_eq!(contribution,if paired {0}else{1});assert_eq!(level[w],index/2);
}

#[kani::proof] #[kani::unwind(34)] fn semantic_zero_high_field(){
 let compact:[u8;16]=kani::any();let row:u8=kani::any();
 let expanded=r::expand_chunk(compact);
 assert_eq!(f::r1_wire::validate_record_fields(row,&expanded).is_ok(),r::canonical_qm(compact));
}
