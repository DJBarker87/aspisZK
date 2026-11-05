use aspis_core::{field::M31,state_only_prefix::r0::Error};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn NHG_field_step(out:&mut Vec<u8>,value:&M31)->Result<(),Error>{
                    if value.0 >= aspis_core::field::P {
                        return Err(Error::Public);
                    }
                    out.extend_from_slice(&value.0.to_le_bytes());
 Ok(())
}
#[kani::proof] #[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NHG_field_append(){
 let n:usize=kani::any();kani::assume(n<=4);
 let mut out=kani::vec::exact_vec::<u8,4>();out.truncate(n);
 let value:u32=kani::any();let bad=value>=2147483647;
 let j:usize=kani::any();kani::assume(j<n+if bad{0}else{4});
 let old=if j<n{out[j]}else{0};
 let got=NHG_field_step(&mut out,&M31(value));
 assert_eq!(got,if bad{Err(Error::Public)}else{Ok(())});
 assert_eq!(out.len(),n+if bad{0}else{4});
 let expected=if j<n{old}else{((value>>((j-n)*8))&255)as u8};
 assert_eq!(out[j],expected^if cfg!(NHG_invert){1}else{0});
}

// One exact KMX_realloc copy-loop iteration, not a replacement copy stub.
#[kani::proof] #[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_realloc_window(){
 use core::mem::MaybeUninit;
 let n:usize=kani::any();kani::assume(n>0&&n<=1880);
 let i:usize=kani::any();kani::assume(i<1884);
 let k:usize=kani::any();kani::assume(k<n);if cfg!(NHG_invert){kani::assume(i==k);}
 let mut src:[MaybeUninit<u8>;1884]=[MaybeUninit::uninit();1884];
 let mut dst:[MaybeUninit<u8>;1884]=[MaybeUninit::uninit();1884];
 let old:u8=kani::any();let value:u8=kani::any();
 dst[k].write(old);if i<n {src[i].write(value);}
 unsafe {
  let ptr=src.as_mut_ptr().cast::<u8>();let out=dst.as_mut_ptr().cast::<u8>();
  let value=ptr.cast::<MaybeUninit<u8>>().add(i).read();
  out.cast::<MaybeUninit<u8>>().add(i).write(value);
 }
 let got=unsafe{dst[k].assume_init()};
 assert_eq!(got,(if k==i{value}else{old})^if cfg!(NHG_invert){1}else{0});
}

// Std append leaf for all serializer tag bytes; arbitrary full prior buffer.
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NHG_std_push(){
 let n:usize=kani::any();kani::assume(n<=1880);let mut out=kani::vec::exact_vec::<u8,1884>();out.truncate(n);let value:u8=kani::any();let j:usize=kani::any();kani::assume(j<n+1);let old=if j<n{out[j]}else{0};
 if cfg!(NHG_invert){kani::assume(j==n);}
 out.push(value);assert_eq!(out.len(),n+1);assert_eq!(out[j],(if j<n{old}else{value})^if cfg!(NHG_invert){1}else{0});
}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NHG_std_push_growth(){
 let n:usize=kani::any();kani::assume(n<=4);let mut out=kani::vec::exact_vec::<u8,4>();out.truncate(n);let value:u8=kani::any();let j:usize=kani::any();kani::assume(j<n+1);let old=if j<n{out[j]}else{0};
 if cfg!(NHG_invert){kani::assume(n==4&&j==n);}
 out.push(value);assert_eq!(out.len(),n+1);assert_eq!(out[j],(if j<n{old}else{value})^if cfg!(NHG_invert){1}else{0});
}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NHG_std_push_new(){
 let value:u8=kani::any();let mut out=Vec::new();out.push(value);assert_eq!(out.len(),1);assert_eq!(out[0],value^if cfg!(NHG_invert){1}else{0});
}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_std_index64(){
 let value:u64=kani::any();let i:usize=kani::any();kani::assume(i<8);let bytes=value.to_le_bytes();assert_eq!(bytes[i],(((value>>(8*i))&255)as u8)^if cfg!(NHG_invert){1}else{0});
}
