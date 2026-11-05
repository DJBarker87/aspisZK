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
 let n:usize=kani::any();kani::assume(n<=1880);
 let mut out=kani::vec::exact_vec::<u8,1884>();out.truncate(n);
 let value:u32=kani::any();let bad=value>=2147483647;
 let j:usize=kani::any();kani::assume(j<n+if bad{0}else{4});
 let old=if j<n{out[j]}else{0};
 let got=NHG_field_step(&mut out,&M31(value));
 assert_eq!(got,if bad{Err(Error::Public)}else{Ok(())});
 assert_eq!(out.len(),n+if bad{0}else{4});
 let expected=if j<n{old}else{((value>>((j-n)*8))&255)as u8};
 assert_eq!(out[j],expected^if cfg!(NHG_invert){1}else{0});
}
