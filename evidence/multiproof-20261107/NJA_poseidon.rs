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

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_windows_header_active(){
 let a:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();kani::assume(at<n&&n<=16&&n-at>=2);let mut it=a[at..n].windows(2);let w=it.next().unwrap();assert_eq!(w.as_ptr(),a[at..].as_ptr());assert_eq!(w.len(),2);
 let mut actual:[usize;3]=unsafe{core::mem::transmute(it)};let expected:[usize;3]=unsafe{core::mem::transmute(a[at+1..n].windows(2))};let k:usize=kani::any();kani::assume(k<3);if cfg!(NJA_bad_argument){actual[k]^=1;}assert_eq!(actual[k],expected[k]);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_windows_header_exit(){
 let a:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();kani::assume(at<=n&&n<=16&&n-at<2);let mut it=a[at..n].windows(2);assert!(it.next().is_none());
 let mut actual:[usize;3]=unsafe{core::mem::transmute(it)};let expected:[usize;3]=unsafe{core::mem::transmute(a[at..n].windows(2))};let k:usize=kani::any();kani::assume(k<3);if cfg!(NJA_bad_argument){actual[k]^=1;}assert_eq!(actual[k],expected[k]);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_iter_header_active(){
 let a:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();kani::assume(at<n&&n<=16);let mut it=a[at..n].iter();assert_eq!(*it.next().unwrap(),a[at]);assert_eq!(it.as_slice().as_ptr(),a[at+1..n].as_ptr());assert_eq!(it.as_slice().len(),n-at-1);
 let mut actual:[usize;2]=unsafe{core::mem::transmute(it)};let expected:[usize;2]=unsafe{core::mem::transmute(a[at+1..n].iter())};let k:usize=kani::any();kani::assume(k<2);if cfg!(NJA_bad_argument){actual[k]^=1;}assert_eq!(actual[k],expected[k]);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_iter_header_exit(){
 let a:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);let mut it=a[n..n].iter();assert!(it.next().is_none());
 let mut actual:[usize;2]=unsafe{core::mem::transmute(it)};let expected:[usize;2]=unsafe{core::mem::transmute(a[n..n].iter())};let k:usize=kani::any();kani::assume(k<2);if cfg!(NJA_bad_argument){actual[k]^=1;}assert_eq!(actual[k],expected[k]);
}
#[kani::proof]
fn NJA_window_predicate(){let a:[u32;16]=kani::any();let at:usize=kani::any();kani::assume(at<15);let mut it=a[at..].windows(2);let w=it.next().unwrap();let out=(|w:&[u32]|w[0]<w[1])(w);let expected=if cfg!(NJA_bad_argument){(a[at]^1)<a[at+1]}else{a[at]<a[at+1]};assert_eq!(out,expected);}
#[kani::proof]
fn NJA_domain_predicate(){let a:[u32;16]=kani::any();let at:usize=kani::any();kani::assume(at<16);let mut it=a[at..].iter();let value=it.next().unwrap();let out=(|&i:&u32|i<(1u32<<18))(value);let expected=if cfg!(NJA_bad_argument){a[at]<=262144}else{a[at]<262144};assert_eq!(out,expected);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::unwind(140)]
fn NJA_count_copy(){let indices:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n<=16&&k<16);let mut level=[0u32;16];level[..n].copy_from_slice(&indices[..n]);if cfg!(NJA_bad_argument){level[k]^=1;}assert_eq!(level[k],if k<n{indices[k]}else{0});}

// One scalar full-round body step; opaque pow5 callee logged above.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_full_round_cell(){
 let mut state=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let constants:[u32;16]=kani::any();let lane:usize=kani::any();let k:usize=kani::any();kani::assume(lane<16&&k<16&&state[lane].0<aspis_core::field::P&&constants[lane]<aspis_core::field::P);let before=state[k];let input=state[lane].add(M31(constants[lane]));let mut log=NJA_empty();state[lane]=NJA_pow5(&mut log,state[lane].add(M31(constants[lane])));if cfg!(NJA_bad_argument){log.events[0].a^=1;}assert_eq!(log.len,3);assert_eq!(log.events[0].a,input.0 as u64);assert_eq!(log.events[0].b,input.0 as u64);assert_eq!(state[k],if k==lane{log.events[2].out}else{before});
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_internal_round_cell(){
 let mut state=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let constant:u32=kani::any();let k:usize=kani::any();kani::assume(k<16&&state[0].0<aspis_core::field::P&&constant<aspis_core::field::P);let before=state[k];let input=state[0].add(M31(constant));let mut log=NJA_empty();state[0]=NJA_pow5(&mut log,state[0].add(M31(constant)));if cfg!(NJA_bad_argument){log.events[0].a^=1;}assert_eq!(log.len,3);assert_eq!(log.events[0].a,input.0 as u64);assert_eq!(log.events[0].b,input.0 as u64);assert_eq!(state[k],if k==0{log.events[2].out}else{before});
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_trace_initial(){
 let state=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let mut input=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let old=input;let index:usize=kani::any();let k:usize=kani::any();kani::assume(index<4&&k<16);let mut round=(0+index) as u8;let mut record=None;
 let mut trace=|e:Poseidon2RoundTransition|{record=Some(e);};
 trace(Poseidon2RoundTransition{round,kind:Poseidon2RoundKind::ExternalInitial(index as u8),input,output:state});round+=1;input=state;
 let e=record.unwrap();if cfg!(NJA_bad_argument){assert_eq!(e.round,(0+index+1) as u8)}else{assert_eq!(e.round,(0+index) as u8)};assert!(matches!(e.kind,Poseidon2RoundKind::ExternalInitial(i) if i==index as u8));assert_eq!(e.input[k],old[k]);assert_eq!(e.output[k],state[k]);assert_eq!(input[k],state[k]);assert_eq!(round,(0+index+1) as u8);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_trace_internal(){
 let state=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let mut input=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let old=input;let index:usize=kani::any();let k:usize=kani::any();kani::assume(index<14&&k<16);let mut round=(4+index) as u8;let mut record=None;
 let mut trace=|e:Poseidon2RoundTransition|{record=Some(e);};
 trace(Poseidon2RoundTransition{round,kind:Poseidon2RoundKind::Internal(index as u8),input,output:state});round+=1;input=state;
 let e=record.unwrap();if cfg!(NJA_bad_argument){assert_eq!(e.round,(4+index+1) as u8)}else{assert_eq!(e.round,(4+index) as u8)};assert!(matches!(e.kind,Poseidon2RoundKind::Internal(i) if i==index as u8));assert_eq!(e.input[k],old[k]);assert_eq!(e.output[k],state[k]);assert_eq!(input[k],state[k]);assert_eq!(round,(4+index+1) as u8);
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_trace_final(){
 let state=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let mut input=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let old=input;let index:usize=kani::any();let k:usize=kani::any();kani::assume(index<4&&k<16);let mut round=(18+index) as u8;let mut record=None;
 let mut trace=|e:Poseidon2RoundTransition|{record=Some(e);};
 trace(Poseidon2RoundTransition{round,kind:Poseidon2RoundKind::ExternalFinal(index as u8),input,output:state});round+=1;input=state;
 let e=record.unwrap();if cfg!(NJA_bad_argument){assert_eq!(e.round,(18+index+1) as u8)}else{assert_eq!(e.round,(18+index) as u8)};assert!(matches!(e.kind,Poseidon2RoundKind::ExternalFinal(i) if i==index as u8));assert_eq!(e.input[k],old[k]);assert_eq!(e.output[k],state[k]);assert_eq!(input[k],state[k]);assert_eq!(round,(18+index+1) as u8);
}

#[kani::proof]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_compress_input(){let left=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let right=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let k:usize=kani::any();kani::assume(k<16&&right[7].0<aspis_core::field::P);let mut state=[M31::ZERO;16];state[..8].copy_from_slice(&left);state[8..].copy_from_slice(&right);state[15]=state[15].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);if cfg!(NJA_bad_argument){state[k].0^=1;}assert_eq!(state[k],if k<8{left[k]}else if k<15{right[k-8]}else{right[7].add(MERKLE_NODE_COMPRESSION_V3_TWEAK)});}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_compress_output(){let state=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let out:[M31;8]=core::array::from_fn(|index|state[index]);let k:usize=kani::any();kani::assume(k<8);if cfg!(NJA_bad_argument){assert_eq!(out[k].0,state[k].0^1)}else{assert_eq!(out[k],state[k])}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJA_chunks_header(){let mut state:[u32;16]=kani::any();let at:usize=kani::any();let k:usize=kani::any();kani::assume(at<=12&&at%4==0&&k<5);let ptr=state.as_mut_ptr();let mut iter=state[at..].chunks_exact_mut(4);let chunk=iter.next().unwrap();assert_eq!(chunk.as_mut_ptr(),unsafe{ptr.add(at)});assert_eq!(chunk.len(),4);let header:[usize;5]=unsafe{core::mem::transmute(iter)};let expected_iter=state[at+4..].chunks_exact_mut(4);let expected:[usize;5]=unsafe{core::mem::transmute(expected_iter)};if cfg!(NJA_bad_argument){assert_eq!(header[k],expected[k]^1)}else{assert_eq!(header[k],expected[k])}}
