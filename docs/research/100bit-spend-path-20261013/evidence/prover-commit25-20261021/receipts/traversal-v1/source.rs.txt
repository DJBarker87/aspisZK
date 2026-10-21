// Relational control gates: every arithmetic cell response is arbitrary and
// shared by ordinal. Ordered cell inputs are retained and compared. These
// gates verify traversal/state wiring, not arithmetic or the complete source.
#[kani::proof]
#[kani::unwind(10)]
fn division_traversal() {
 let words: [u32;8] = kani::any();
 let quotients: [u32;8] = kani::any();
 let remainders: [u64;8] = kani::any();
 let mut a = words; let mut b = words;
 let mut ra = 0u64; let mut rb = 0u64;
 let mut inputs_a = [(0u64,0u32);8];
 let mut inputs_b = [(0u64,0u32);8];
 let mut i=0;
 for limb in a.iter_mut().rev() {
  inputs_a[i]=(ra,*limb);
  *limb=quotients[i]; ra=remainders[i]; i+=1;
 }
 let mut j=8usize; let mut i=0;
 while j>0 {
  j-=1;
  inputs_b[i]=(rb,b[j]);
  b[j]=quotients[i]; rb=remainders[i]; i+=1;
 }
 assert_eq!(ra,rb);
 for i in 0..8 {
  assert_eq!(a[i],b[i]);
  assert_eq!(inputs_a[i].0,inputs_b[i].0);
  assert_eq!(inputs_a[i].1,inputs_b[i].1);
 }
}
#[kani::proof]
#[kani::unwind(10)]
fn lowdigits_outer_traversal() {
 let block: [u8;32] = kani::any();
 let a: [u32;8] = core::array::from_fn(|i|
  u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap()));
 let mut b=[0u32;8];let mut i=0;
 while i<8 {let start=4*i;b[i]=u32::from_le_bytes([
  block[start],block[start+1],block[start+2],block[start+3]]);i+=1;}
 let pass_words: [[u32;8];8]=kani::any();
 let pass_digits: [u32;8]=kani::any();
 let mut quotient=a;let mut rank=b;
 let mut inputs_a=[[0u32;8];8];let mut inputs_b=[[0u32;8];8];
 let mut n=0;
 let digits_a: [u32;8]=core::array::from_fn(|_| {
  inputs_a[n]=quotient; quotient=pass_words[n];let digit=pass_digits[n];n+=1;digit
 });
 let mut digits_b=[0u32;8];let mut i=0;
 while i<8 {inputs_b[i]=rank;rank=pass_words[i];digits_b[i]=pass_digits[i];i+=1;}
 for i in 0..8 {
  assert_eq!(a[i],b[i]); assert_eq!(digits_a[i],digits_b[i]);
  for j in 0..8 {assert_eq!(inputs_a[i][j],inputs_b[i][j]);}
 }
 assert_eq!(quotient[0],rank[0]);
}
