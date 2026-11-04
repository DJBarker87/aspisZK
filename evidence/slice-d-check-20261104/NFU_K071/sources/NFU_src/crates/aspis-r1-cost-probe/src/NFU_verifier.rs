// OPEN one-iteration oracle candidate; no claimed actual Dot ABI transport.
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log{reply:bool,after:[u64;9],before:[u64;9],value:[u32;8],scalar:[u32;4],calls:usize,order:u8,field_ptr:*const u8,field_len:usize,field_index:usize,weight_ptr:*const K,weight_index:usize}
fn recorded_push(dot:&mut crate::fast_pairing::EbyKDot,value:E,scalar:K,log:&mut Log)->Result<(),()>{log.before=crate::fast_pairing::NFU_helpers::read(dot);log.value=value.to_limbs();log.scalar=[scalar.c0.a.0,scalar.c0.b.0,scalar.c1.a.0,scalar.c1.b.0];log.calls+=1;log.order=if log.order==2{3}else{255};*dot=crate::fast_pairing::NFU_helpers::make(log.after);if log.reply{Ok(())}else{Err(())}}
fn recorded_field(bytes:&[u8],j:usize,log:&mut Log)->E{let selected=&bytes[32*j..32*(j+1)];log.field_ptr=selected.as_ptr();log.field_len=selected.len();log.field_index=j;log.order=1;field(bytes,j)}
fn recorded_weight(weights:&[K],j:usize,log:&mut Log)->K{log.weight_ptr=&weights[j];log.weight_index=j;log.order=if log.order==1{2}else{255};weights[j]}
fn source_step(final_message:&[u8],weights:&[K],dot:&mut crate::fast_pairing::EbyKDot,j:&mut usize,log:&mut Log)->Result<(),Error>{
 let value=recorded_field(final_message,*j,log);
 let scalar=recorded_weight(weights,*j,log);
 recorded_push(dot,value,scalar,log).map_err(|_|Error::Parse)?;*j+=1;Ok(())
}
fn exercise(group:u8){
 let mut bytes:[u8;2048]=kani::any();let j:usize=kani::any();kani::assume(j<64);
 let value:[u32;8]=kani::any();for x in value{kani::assume(x<0x7fffffff);}
 for i in 0..8{bytes[32*j+4*i..32*j+4*i+4].copy_from_slice(&value[i].to_le_bytes());}
 let scalar:[u32;4]=kani::any();let mut weights=[K::ZERO;64];weights[j]=K{c0:aspis_core::field::CM31{a:M31(scalar[0]),b:M31(scalar[1])},c1:aspis_core::field::CM31{a:M31(scalar[2]),b:M31(scalar[3])}};
 let before:[u64;9]=kani::any();let after:[u64;9]=kani::any();let reply:bool=kani::any();
 let mut log=Log{reply,after,before:[0;9],value:[0;8],scalar:[0;4],calls:0,order:0,field_ptr:core::ptr::null(),field_len:0,field_index:0,weight_ptr:core::ptr::null(),weight_index:0};
 let mut dot=crate::fast_pairing::NFU_helpers::make(before);let mut index=j;let result=source_step(&bytes,&weights,&mut dot,&mut index,&mut log);let final_state=crate::fast_pairing::NFU_helpers::read(&dot);
 let good=match group{
 0=>if reply{matches!(result,Ok(()))}else{matches!(result,Err(Error::Parse))},
 1=>index==if reply{j+1}else{j},2=>log.calls==1,3=>log.before==before,4=>final_state==after,
 5=>log.value[..4]==value[..4],6=>log.value[4..]==value[4..],7=>log.scalar==scalar,
 8=>log.value.iter().all(|x|*x<0x7fffffff),9=>log.order==3,
 10=>log.field_ptr==bytes.as_ptr().wrapping_add(32*j),11=>log.field_len==32,
 12=>log.field_index==j,13=>log.weight_ptr==weights.as_ptr().wrapping_add(j)&&log.weight_index==j,
 _=>false};assert!(good != cfg!(NFU_invert));
}
macro_rules! gate{($name:ident,$n:expr)=>{#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){exercise($n)}};}
gate!(finish_g00,0);
gate!(finish_g01,1);
gate!(finish_g02,2);
gate!(finish_g03,3);
gate!(finish_g04,4);
gate!(finish_g05,5);
gate!(finish_g06,6);
gate!(finish_g07,7);
gate!(finish_g08,8);
gate!(finish_g09,9);
gate!(finish_g10,10);
gate!(finish_g11,11);
gate!(finish_g12,12);
gate!(finish_g13,13);
