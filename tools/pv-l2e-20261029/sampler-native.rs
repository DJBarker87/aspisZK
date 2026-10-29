mod raw;
const P:u64=2147483647;
fn pass(mut q:[u32;8])->([u32;8],u32) {
 let mut rem=0u64;
 for j in (0..8).rev() {
  let d=rem*4294967296+q[j] as u64;
  q[j]=(d/P) as u32; rem=d%P;
 }
 (q,rem as u32)
}
fn digits(block:[u8;32],n:usize)->([u32;8],Vec<u32>) {
 let mut q=[0;8]; for i in 0..8 {q[i]=u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap());}
 let mut ds=vec![];
 for _ in 0..n {let (next,d)=pass(q);q=next;ds.push(d);}
 (q,ds)
}
fn carry(mut ds:[u32;8],mut a:u32)->([u32;8],bool) {
 for d in &mut ds {let sum=*d as u64+a as u64;*d=(sum%P) as u32;a=(sum/P) as u32;}
 (ds,a!=0)
}
fn check(b:[u8;32],negative:bool) {
 let (q,ds)=digits(b,8);
 let (got,hi)=raw::low(&b);
 assert_eq!(got,ds.as_slice()); assert_eq!(hi,q[0]); assert!(q[1..].iter().all(|&x|x==0));assert!(hi<=256);
 let (q4,d4)=digits(b,4);let _=q4;assert_eq!(raw::qm(&b),d4.as_slice());
 let (mut want,wrap)=carry(got,hi+1);
 let mut out=got;let gotwrap=raw::add(&mut out,hi+1);assert_eq!((out,gotwrap),(want,wrap));
 if wrap {let (w,again)=carry(want,1);assert!(!again);let native_again=raw::add(&mut out,1);assert!(!native_again);want=w;}
 assert_eq!(out,want);
 if negative {assert_eq!(hi.wrapping_add(1),q[0]);}
}
fn main(){
 let negative=std::env::args().any(|x|x=="negative");
 let mut count=0u64;
 for byte in 0..=255u8 {check([byte;32],negative);count+=1;}
 let mut seed=0x8ad30ba6e41b741cu64;
 for _ in 0..10000 {let mut b=[0;32];for x in &mut b {seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;*x=seed as u8;}check(b,negative);count+=1;}
 for shape in 0..256u32 {for a in 0..=257u32 {let mut ds=[0;8];for i in 0..8 {ds[i]=if shape>>i&1==0 {0}else{P as u32-1};}let want=carry(ds,a);let mut got=ds;let w=raw::add(&mut got,a);assert_eq!((got,w),want);count+=1;}}
 println!("PASS {count} finite full-state sampler/carry comparisons");
}
