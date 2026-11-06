use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct NJA_Event { kind:u8, a:u64, b:u64, out:M31 }
struct NJA_Log { events:[NJA_Event;4], len:usize }
fn NJA_empty()->NJA_Log{NJA_Log{events:[NJA_Event{kind:0,a:0,b:0,out:M31(0)};4],len:0}}
fn NJA_product(log:&mut NJA_Log,a:M31,b:M31)->M31{
 assert!(a.0<aspis_core::field::P&&b.0<aspis_core::field::P&&log.len<4);
 let out=M31(kani::any());kani::assume(out.0<aspis_core::field::P);
 log.events[log.len]=NJA_Event{kind:0,a:a.0 as u64,b:b.0 as u64,out};log.len+=1;out
}
fn NJA_reduce(log:&mut NJA_Log,a:u64)->M31{
 assert!(a<(1u64<<62)&&log.len<4);
 let out=M31(kani::any());kani::assume(out.0<aspis_core::field::P);
 log.events[log.len]=NJA_Event{kind:1,a,b:0,out};log.len+=1;out
}
// Source-equivalent opaque-call form; natural product values are installed by
// NJA_FieldLaws.generated_mul and pow5_value, never verified by Kani.
fn NJA_pow5(log:&mut NJA_Log,value:M31)->M31{
 let square=NJA_product(log,value,value);
 let fourth=NJA_product(log,square,square);
 NJA_product(log,fourth,value)
}
fn NJA_mat4(log:&mut NJA_Log,values:&mut[M31]){
 let a=values[0].0 as u64;let b=values[1].0 as u64;let c=values[2].0 as u64;let d=values[3].0 as u64;
 values[0]=NJA_reduce(log,2*a+3*b+c+d);
 values[1]=NJA_reduce(log,a+2*b+3*c+d);
 values[2]=NJA_reduce(log,a+b+2*c+3*d);
 values[3]=NJA_reduce(log,3*a+b+c+2*d);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_copy(){let src:[u8;128]=kani::any();let mut dst=[0u8;128];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),128)};let k:usize=kani::any();kani::assume(k<128);if cfg!(NJA_bad_argument){assert_eq!(dst[k],src[k]^1)}else{assert_eq!(dst[k],src[k])}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_pow5_log(){
 let value=M31(kani::any());kani::assume(value.0<aspis_core::field::P);let mut log=NJA_empty();let out=NJA_pow5(&mut log,value);
 if cfg!(NJA_bad_argument){log.events[0].a^=1;}
 assert_eq!(log.len,3);assert_eq!(log.events[0].kind,0);assert_eq!(log.events[0].a,value.0 as u64);assert_eq!(log.events[0].b,value.0 as u64);
 assert_eq!(log.events[1].kind,0);assert_eq!(log.events[1].a,log.events[0].out.0 as u64);assert_eq!(log.events[1].b,log.events[0].out.0 as u64);
 assert_eq!(log.events[2].kind,0);assert_eq!(log.events[2].a,log.events[1].out.0 as u64);assert_eq!(log.events[2].b,value.0 as u64);assert_eq!(out,log.events[2].out);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_mat4_log(){
 let raw:[u32;5]=kani::any();kani::assume(raw[0]<aspis_core::field::P&&raw[1]<aspis_core::field::P&&raw[2]<aspis_core::field::P&&raw[3]<aspis_core::field::P);
 let mut values=[M31(raw[0]),M31(raw[1]),M31(raw[2]),M31(raw[3]),M31(raw[4])];let a=raw[0] as u64;let b=raw[1] as u64;let c=raw[2] as u64;let d=raw[3] as u64;
 let mut log=NJA_empty();NJA_mat4(&mut log,&mut values);if cfg!(NJA_bad_argument){log.events[0].a^=1;}
 assert_eq!(log.len,4);assert_eq!(log.events[0].a,2*a+3*b+c+d);assert_eq!(log.events[1].a,a+2*b+3*c+d);assert_eq!(log.events[2].a,a+b+2*c+3*d);assert_eq!(log.events[3].a,3*a+b+c+2*d);
 let k:usize=kani::any();kani::assume(k<4);assert_eq!(log.events[k].kind,1);assert_eq!(values[k],log.events[k].out);assert_eq!(values[4],M31(raw[4]));
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_mat4_log4(){
 let raw:[u32;4]=kani::any();kani::assume(raw[0]<aspis_core::field::P&&raw[1]<aspis_core::field::P&&raw[2]<aspis_core::field::P&&raw[3]<aspis_core::field::P);
 let mut values=[M31(raw[0]),M31(raw[1]),M31(raw[2]),M31(raw[3])];let a=raw[0] as u64;let b=raw[1] as u64;let c=raw[2] as u64;let d=raw[3] as u64;
 let mut log=NJA_empty();NJA_mat4(&mut log,&mut values);if cfg!(NJA_bad_argument){log.events[0].a^=1;}
 assert_eq!(log.len,4);assert_eq!(log.events[0].a,2*a+3*b+c+d);assert_eq!(log.events[1].a,a+2*b+3*c+d);assert_eq!(log.events[2].a,a+b+2*c+3*d);assert_eq!(log.events[3].a,3*a+b+c+2*d);
 let k:usize=kani::any();kani::assume(k<4);assert_eq!(log.events[k].kind,1);assert_eq!(values[k],log.events[k].out);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_external_chunk(){
 let raw:[u32;16]=kani::any();let mut state=[M31(raw[0]),M31(raw[1]),M31(raw[2]),M31(raw[3]),M31(raw[4]),M31(raw[5]),M31(raw[6]),M31(raw[7]),M31(raw[8]),M31(raw[9]),M31(raw[10]),M31(raw[11]),M31(raw[12]),M31(raw[13]),M31(raw[14]),M31(raw[15])];let group:usize=kani::any();let k:usize=kani::any();kani::assume(group<4&&k<16);let start=4*group;
 kani::assume(raw[start]<aspis_core::field::P&&raw[start+1]<aspis_core::field::P&&raw[start+2]<aspis_core::field::P&&raw[start+3]<aspis_core::field::P);
 let a=raw[start] as u64;let b=raw[start+1] as u64;let c=raw[start+2] as u64;let d=raw[start+3] as u64;let before=state[k];let mut log=NJA_empty();
 let mut chunks=state[start..].chunks_exact_mut(4);let chunk=chunks.next().unwrap();assert_eq!(chunk.len(),4);NJA_mat4(&mut log,chunk);
 if cfg!(NJA_bad_argument){log.events[0].a^=1;}
 assert_eq!(log.len,4);assert_eq!(log.events[0].a,2*a+3*b+c+d);assert_eq!(log.events[1].a,a+2*b+3*c+d);assert_eq!(log.events[2].a,a+b+2*c+3*d);assert_eq!(log.events[3].a,3*a+b+c+2*d);
 assert_eq!(state[k],if start<=k&&k<start+4{log.events[k-start].out}else{before});
}
#[kani::proof]
fn NJA_external_sum(){
 let state:[u32;16]=kani::any();let row:usize=kani::any();let column:usize=kani::any();let mut sum:u64=kani::any();kani::assume(row<4&&column<4&&sum<=row as u64*(aspis_core::field::P as u64)&&state[4*row+column]<aspis_core::field::P);let before=sum;let selected=state[4*row+column] as u64;
 sum+=state[4*row+column] as u64;
 if cfg!(NJA_bad_argument){sum^=1;}
 assert_eq!(sum,before+selected);assert!(sum<=(row as u64+1)*(aspis_core::field::P as u64));
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_external_cell(){
 let raw:[u32;16]=kani::any();let mut state=[M31(raw[0]),M31(raw[1]),M31(raw[2]),M31(raw[3]),M31(raw[4]),M31(raw[5]),M31(raw[6]),M31(raw[7]),M31(raw[8]),M31(raw[9]),M31(raw[10]),M31(raw[11]),M31(raw[12]),M31(raw[13]),M31(raw[14]),M31(raw[15])];let sums:[u64;4]=kani::any();let index:usize=kani::any();let k:usize=kani::any();kani::assume(index<16&&k<16&&raw[index]<aspis_core::field::P&&sums[index&3]<=4*(aspis_core::field::P as u64));let before=state[k];let input=state[index].0 as u64+sums[index&3];let mut log=NJA_empty();
 state[index]=NJA_reduce(&mut log,state[index].0 as u64+sums[index&3]);
 if cfg!(NJA_bad_argument){log.events[0].a^=1;}
 assert_eq!(log.len,1);assert_eq!(log.events[0].kind,1);assert_eq!(log.events[0].a,input);assert_eq!(state[k],if k==index{log.events[0].out}else{before});
}
#[kani::proof]
fn NJA_external_chunks_exit(){let mut state:[u32;16]=kani::any();let mut chunks=state[16..].chunks_exact_mut(4);let out=chunks.next();if cfg!(NJA_bad_argument){assert!(out.is_some())}else{assert!(out.is_none())}}
#[kani::proof]
fn NJA_internal_sum(){
 let state:[u32;16]=kani::any();let index:usize=kani::any();let mut sum:u64=kani::any();kani::assume(1<=index&&index<16&&sum<=(index as u64-1)*(aspis_core::field::P as u64)&&state[index]<aspis_core::field::P);let before=sum;let selected=state[index] as u64;
 sum+=state[index] as u64;
 if cfg!(NJA_bad_argument){sum^=1;}
 assert_eq!(sum,before+selected);assert!(sum<=index as u64*(aspis_core::field::P as u64));
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_internal_zero(){
 let raw:[u32;16]=kani::any();let mut state=[M31(raw[0]),M31(raw[1]),M31(raw[2]),M31(raw[3]),M31(raw[4]),M31(raw[5]),M31(raw[6]),M31(raw[7]),M31(raw[8]),M31(raw[9]),M31(raw[10]),M31(raw[11]),M31(raw[12]),M31(raw[13]),M31(raw[14]),M31(raw[15])];let part_sum:u64=kani::any();let k:usize=kani::any();kani::assume(k<16&&raw[0]<aspis_core::field::P&&part_sum<=15*(aspis_core::field::P as u64));let before=state[k];let original=state[0].0;let full_sum=part_sum+state[0].0 as u64;let mut log=NJA_empty();
 state[0]=NJA_reduce(&mut log,part_sum+aspis_core::field::P as u64-state[0].0 as u64);
 if cfg!(NJA_bad_argument){log.events[0].a^=1;}
 assert_eq!(full_sum,part_sum+original as u64);assert!(full_sum<=16*(aspis_core::field::P as u64));assert_eq!(log.len,1);assert_eq!(log.events[0].a,part_sum+aspis_core::field::P as u64-original as u64);assert_eq!(state[k],if k==0{log.events[0].out}else{before});
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_internal_cell(){
 let raw:[u32;16]=kani::any();let mut state=[M31(raw[0]),M31(raw[1]),M31(raw[2]),M31(raw[3]),M31(raw[4]),M31(raw[5]),M31(raw[6]),M31(raw[7]),M31(raw[8]),M31(raw[9]),M31(raw[10]),M31(raw[11]),M31(raw[12]),M31(raw[13]),M31(raw[14]),M31(raw[15])];let full_sum:u64=kani::any();let index:usize=kani::any();let k:usize=kani::any();kani::assume(1<=index&&index<16&&k<16&&raw[index]<aspis_core::field::P&&full_sum<=16*(aspis_core::field::P as u64));let before=state[k];let original=state[index].0;let mut log=NJA_empty();
 state[index]=NJA_reduce(&mut log,full_sum+((state[index].0 as u64)<<INTERNAL_SHIFTS[index-1]));
 if cfg!(NJA_bad_argument){log.events[0].a^=1;}
 assert_eq!(log.len,1);assert_eq!(log.events[0].a,full_sum+((original as u64)<<INTERNAL_SHIFTS[index-1]));assert_eq!(state[k],if k==index{log.events[0].out}else{before});
}
