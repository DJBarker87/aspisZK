mod half_prefix_gate {
#[derive(Clone,Copy)]struct Inputs{public:bool,prefix:Option<u8>,certificate:bool,convert:bool,builders:bool,check:bool,panic:bool}
fn emit(i:Inputs)->Option<u8>{let h=match i.prefix{Some(x)=>x,None=>return None};if !i.certificate{return None;}Some(h)}
fn native(i:Inputs)->bool{let verdict=if i.panic{Err(())}else{Ok((||->Option<bool>{if !i.public{return None;}let cert=emit(i);let _cert=cert?;if !i.convert||!i.builders{return None;}Some(i.check)})())};matches!(verdict,Ok(Some(true)))}
#[cfg(kani)]mod proofs{use super::*;
#[kani::proof]fn accepted_prefix(){let i=Inputs{public:kani::any(),prefix:kani::any(),certificate:kani::any(),convert:kani::any(),builders:kani::any(),check:kani::any(),panic:kani::any()};if native(i){assert!(i.prefix.is_some());}}
}
}
