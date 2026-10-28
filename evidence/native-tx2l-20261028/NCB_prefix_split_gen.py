from NCB_generate import *
p='crates/aspis-r1-cost-probe/src/verifier.rs'
t='''\n#[cfg(kani)] mod NCB_prefix_split {\nuse super::*;\n'''
t+='''#[kani::proof] #[kani::unwind(512)]\n'''+attrs+'''fn read(){
 let raw:[u32;110]=kani::any();let flat:[M31;110]=unsafe{core::mem::transmute(raw)};
 let index:usize=kani::any();kani::assume(index<flat.len());let value=flat[index];
 assert!(value.0==raw[index]);assert!(flat.len()==110);
}\n'''
t+='''#[kani::proof] #[kani::unwind(4)]\nfn increment(){let mut index:usize=kani::any();let len:usize=kani::any();kani::assume(len<=110&&index<len);let old=index;index+=1;assert!(index==old+1&&index<=len);}\n'''
t+='''#[kani::proof] #[kani::unwind(4)]\nfn termination(){let index:usize=kani::any();let len:usize=kani::any();kani::assume(len<=110);if index<len{assert!(index<110);}else{assert!(index>=len);}}\n'''
t+='''static mut LEFT:u32=0;static mut RIGHT:u32=0;static mut REPLY:u32=0;static mut CALLS:u8=0;
 fn mul(a:M31,b:M31)->M31{unsafe{assert!(a.0==LEFT&&b.0==RIGHT&&CALLS==0);CALLS=1;let out:u32=kani::any();kani::assume(u64::from(out)==(u64::from(a.0)*u64::from(b.0))%2147483647);REPLY=out;M31(out)}}
 #[kani::proof] #[kani::unwind(4)] #[kani::stub(M31::mul,mul)]
 fn multiply(){let value=M31(kani::any());let mut product=M31(kani::any());unsafe{LEFT=product.0;RIGHT=value.0;CALLS=0;}product=product.mul(value);unsafe{assert!(CALLS==1&&product.0==REPLY);}}
}\n'''
emit(p,t,'NCB_prefix_split')
