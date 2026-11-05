use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// One literal iteration of frozen BatchedWeights::new. No loop is unrolled.
fn pending_step(weights:&[K],raw:&mut Vec<[u64;4]>,mut index:usize)->usize{
 let w=weights[index];
 raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
 index+=1;
 index
}
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pending_iteration(){
 let index:usize=kani::any();kani::assume(index<64);
 let j:usize=kani::any();kani::assume(j<64);
 let limbs:[u32;4]=kani::any();
 let w=K{c0:aspis_core::field::CM31{a:M31(limbs[0]),b:M31(limbs[1])},c1:aspis_core::field::CM31{a:M31(limbs[2]),b:M31(limbs[3])}};
 let mut weights=[K::ZERO;64];weights[index]=w;let before_weight=weights[j];
 let input:[[u64;4];64]=kani::any();let mut raw=Vec::from(input);let before=raw[j];
 let addr=raw.as_ptr();let cap=raw.capacity();let next=pending_step(&weights,&mut raw,index);
 let expected=if j==index{[limbs[0] as u64,limbs[1] as u64,limbs[2] as u64,limbs[3] as u64]}else{before};
 let good=next==index+1&&raw[j]==expected&&raw.len()==64&&raw.capacity()==cap&&raw.as_ptr()==addr&&weights[j]==before_weight;
 assert!(good!=cfg!(NHS_invert));
}
fn pending_return(raw:Vec<[u64;4]>)->BatchedWeights{BatchedWeights{raw,terms:0}}
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pending_record(){
 let input:[[u64;4];64]=kani::any();let raw=Vec::from(input);let at:usize=kani::any();kani::assume(at<64);
 let value=raw[at];let ptr=raw.as_ptr();let cap=raw.capacity();let out=pending_return(raw);
 let good=out.terms==0&&out.raw.as_ptr()==ptr&&out.raw.len()==64&&out.raw.capacity()==cap&&out.raw[at]==value;
 assert!(good!=cfg!(NHS_invert));
}
// Heap reply is the local observed filled result. Allocation failure is retained.
fn allocation_cut(reply:Result<Vec<[u64;4]>,aspis_core::r0::Error>)->Result<(Vec<[u64;4]>,usize),Error>{
 let raw=reply.map_err(|_|Error::Allocation)?;
 let index=0;
 Ok((raw,index))
}
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pending_allocation(){
 let failed:bool=kani::any();let raw=Vec::from(kani::any::<[[u64;4];64]>());let ptr=raw.as_ptr();let cap=raw.capacity();
 let at:usize=kani::any();kani::assume(at<64);let value=raw[at];
 let reply=if failed{Err(aspis_core::r0::Error::Allocation)}else{Ok(raw)};
 let out=allocation_cut(reply);
 let good=match out{Err(e)=>failed&&e==Error::Allocation,Ok((raw,index))=>!failed&&index==0&&raw.as_ptr()==ptr&&raw.len()==64&&raw.capacity()==cap&&raw[at]==value};
 assert!(good!=cfg!(NHS_invert));
}
