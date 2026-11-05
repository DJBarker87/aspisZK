use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn k()->K{let x:[u32;4]=kani::any();K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn e()->E{E::new(k(),k())}
fn kw(x:K,j:usize)->u32{match j&3{0=>x.c0.a.0,1=>x.c0.b.0,2=>x.c1.a.0,_=>x.c1.b.0}}
fn ew(x:E,j:usize)->u32{kw(if j<4{x.c0()}else{x.c1()},j)}
fn prepared()->Prepared{Prepared{variant:Variant::S2,roots:kani::any(),gamma:e(),kappa:e(),alpha:[e(),e()],rho:k(),queries:kani::any(),semantic_alpha:[k(),k(),k(),k(),k(),k(),k(),k(),k(),k()],z:[SecureCirclePoint{x:k(),y:k()},SecureCirclePoint{x:k(),y:k()}],claim:e(),state:kani::any()}}
fn finish(p:Prepared,mut a:Accumulator,end:usize,at2:usize,next:u8,allocation:&mut usize)->Result<(Box<Prepared>,Accumulator),Error>{
 if at2!=end{return Err(Error::Checkpoint);}
 a.next=next as usize;
 let boxed=Box::new(p);*allocation=boxed.as_ref() as *const Prepared as usize;Ok((boxed,a))
}
fn check(){
 let p=prepared();
 // Arbitrary valid prestate only; the map initializes the harness input, not a verifier loop.
 let raw=kani::vec::any_vec::<[u32;4],64>();kani::assume(raw.len()==64);
 let weights:alloc::vec::Vec<K>=raw.into_iter().map(|x|K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}).collect();
 let wi:usize=kani::any();kani::assume(wi<64);let j:usize=kani::any();kani::assume(j<8);
 let selected=kw(weights[wi],j);let pointer=weights.as_ptr() as usize;let capacity=weights.capacity();
 let a=Accumulator{weights,rhs:e(),power:k(),next:kani::any()};let next_byte:u8=kani::any();let end:usize=kani::any();let at2:usize=kani::any();
 let roots=p.roots;let gamma=p.gamma;let kappa=p.kappa;let alpha=p.alpha;let rho=p.rho;let queries=p.queries;let semantic=p.semantic_alpha;let z=p.z;let claim=p.claim;let state=p.state;let rhs=a.rhs;let power=a.power;
 let mut allocation=0;let result=finish(p,a,end,at2,next_byte,&mut allocation);
 if at2!=end{assert!(matches!(result,Err(Error::Checkpoint)));assert_eq!(allocation,0);return;}
 let (out,mut after)=result.unwrap();
 if cfg!(NIY_invert){after.weights[wi].c0.a.0^=1;after.weights[wi].c0.b.0^=1;after.weights[wi].c1.a.0^=1;after.weights[wi].c1.b.0^=1;}
 let b:usize=kani::any();kani::assume(b<32);let q:usize=kani::any();kani::assume(q<22);let sem:usize=kani::any();kani::assume(sem<10);let i:usize=kani::any();kani::assume(i<2);
 assert_eq!(out.as_ref() as *const Prepared as usize,allocation);
 assert_eq!(out.variant,Variant::S2);assert_eq!(out.roots[i][b],roots[i][b]);assert_eq!(ew(out.gamma,j),ew(gamma,j));assert_eq!(ew(out.kappa,j),ew(kappa,j));assert_eq!(ew(out.alpha[i],j),ew(alpha[i],j));assert_eq!(kw(out.rho,j),kw(rho,j));assert_eq!(out.queries[q],queries[q]);assert_eq!(kw(out.semantic_alpha[sem],j),kw(semantic[sem],j));assert_eq!(kw(out.z[i].x,j),kw(z[i].x,j));assert_eq!(kw(out.z[i].y,j),kw(z[i].y,j));assert_eq!(ew(out.claim,j),ew(claim,j));assert_eq!(out.state[b],state[b]);assert_eq!(ew(after.rhs,j),ew(rhs,j));assert_eq!(kw(after.power,j),kw(power,j));assert_eq!(after.next,next_byte as usize);assert_eq!(after.weights.as_ptr() as usize,pointer);assert_eq!(after.weights.len(),64);assert_eq!(after.weights.capacity(),capacity);assert_eq!(kw(after.weights[wi],j),selected);
}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn ctor_payload(){check();}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn ctor_payload_renamed(){check();}
