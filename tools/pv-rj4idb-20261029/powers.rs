use aspis_core::field::{WideExact as W,QM31,CM31,M31};
#[path="powers-source.rs"] mod deployed;
fn original<const N:usize>(x:W)->[W;N]{
 let mut out=[W::ZERO;N];let mut p=W::ONE;let mut i=0;
 while i<N{out[i]=p;i+=1;if i==N{return out;}p=p.mul(x);}out
}
fn next(s:&mut u64)->u32{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s as u32}
fn q(s:&mut u64)->QM31{QM31{c0:CM31{a:M31(next(s)),b:M31(next(s))},c1:CM31{a:M31(next(s)),b:M31(next(s))}}}
fn check<const N:usize>(x:W){let y=deployed::powers::<N>(x);assert_eq!(y,original::<N>(x));for i in 1..N{assert_eq!(y[i],y[i-1].mul(x));}}
fn main(){
 let mut s=0x4d448254u64;let mut pairs=0;
 for _ in 0..4096{let x=W::new(q(&mut s),q(&mut s));
 check::<0>(x);check::<1>(x);check::<2>(x);check::<3>(x);check::<16>(x);check::<29>(x);check::<64>(x);check::<255>(x);pairs+=8;}
 assert_eq!(deployed::powers::<1>(W::ZERO),[W::ONE]);
 assert_eq!(deployed::powers::<2>(W::ZERO),[W::ONE,W::ZERO]);
 let z=deployed::powers::<29>(W::ZERO);assert_eq!(z[0],W::ONE);assert!(z[1..].iter().all(|x|*x==W::ZERO));
 let one=deployed::powers::<29>(W::ONE);assert_eq!(one,[W::ONE;29]);
 let mut bad=one;bad[28]=W::ZERO;assert_ne!(bad,one);
 println!("{{\"pairs\":{},\"deployed_N\":29,\"restoration\":true,\"negative_control\":true,\"pass\":true}}",pairs);
}
