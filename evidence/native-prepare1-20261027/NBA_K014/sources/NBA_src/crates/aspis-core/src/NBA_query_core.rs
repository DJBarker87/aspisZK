use super::*;
// ONE source word transition on the actual private QueryScan carrier.
// The pure Std contains call is abstracted by every Bool; the cohort binds
// this parameter to membership in the SAME accepted prefix.
fn NBA_word_step(s:&mut QueryScan,candidate:u32,member:bool)->bool{
 if s.accepted_len==QUERY_COUNT||s.draws==QUERY_MAX_DRAWS{return true;}
 s.draws+=1;
 if !member{s.accepted[s.accepted_len]=candidate;s.accepted_len+=1;}
 false
}
#[kani::proof] #[kani::unwind(3)]
fn NBA_step(){
 let a:[u32;22]=unsafe{core::mem::transmute::<[u8;88],[u32;22]>(kani::any())};let len:usize=kani::any();let draws:usize=kani::any();kani::assume(len<=22&&draws<=64);let candidate:u32=kani::any();let member:bool=kani::any();let mut s=QueryScan{accepted:a,accepted_len:len,draws};
 let stop=NBA_word_step(&mut s,candidate,member);let i:usize=kani::any();kani::assume(i<22);
 if len==22||draws==64{assert!(stop);assert_eq!(s.accepted_len,len);assert_eq!(s.draws,draws);assert_eq!(s.accepted[i],a[i]);kani::cover!(true,"stopped word leaves whole scan unchanged");}
 else{assert!(!stop);assert_eq!(s.draws,draws+1);assert_eq!(s.accepted_len,if member{len}else{len+1});assert_eq!(s.accepted[i],if !member&&i==len{candidate}else{a[i]});kani::cover!(!member,"fresh word");kani::cover!(member,"duplicate word");}
}
#[kani::proof] #[kani::unwind(3)]
fn NBA_finish(){
 let a:[u32;22]=unsafe{core::mem::transmute::<[u8;88],[u32;22]>(kani::any())};let len:usize=kani::any();let draws:usize=kani::any();kani::assume(len<=22&&draws<=64);let s=QueryScan{accepted:a,accepted_len:len,draws};let result=s.finish();
 match result{Ok(out)=>{assert_eq!(len,22);let i:usize=kani::any();kani::assume(i<22);assert_eq!(out[i],a[i]);kani::cover!(true,"finish success");},Err(QuerySampleError::DrawLimitExhausted{accepted,max_draws})=>{assert!(len<22);assert_eq!(accepted,len);assert_eq!(max_draws,64);kani::cover!(true,"finish rejection");},_=>panic!("unreachable finish error")}
}
// Exact single callback expression from block_rank plus query_words mask.
fn NBA_word(block:&[u8;32],i:usize)->u32{let j=4*i;u32::from_le_bytes([block[j],block[j+1],block[j+2],block[j+3]])&(QUERY_BOUND-1)}
#[kani::proof] #[kani::unwind(3)]
fn NBA_word_decode(){
 let b:[u8;32]=kani::any();let i:usize=kani::any();kani::assume(i<8);let got=NBA_word(&b,i);let j=4*i;
 let n=u64::from(b[j])+256*u64::from(b[j+1])+65536*u64::from(b[j+2])+16777216*u64::from(b[j+3]);
 assert_eq!(u64::from(got),n%262144);assert!(got<262144);kani::cover!(true,"arbitrary selected masked word");
}
fn NBA_outer_step(k:usize,stop:bool,advances:&[[u8;32];8],selected:&mut[u8;32])->bool{if stop{*selected=advances[k];return true;}false}
#[kani::proof] #[kani::unwind(3)]
fn NBA_driver_step(){
 let advances:[[u8;32];8]=unsafe{core::mem::transmute::<[u8;256],[[u8;32];8]>(kani::any())};let old:[u8;32]=kani::any();let mut selected=old;let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<8&&j<32);let stop:bool=kani::any();let result=NBA_outer_step(k,stop,&advances,&mut selected);assert_eq!(result,stop);assert_eq!(selected[j],if stop{advances[k][j]}else{old[j]});kani::cover!(stop,"first stop selects this same advance");kani::cover!(!stop,"continuing iteration preserves selection");
}
