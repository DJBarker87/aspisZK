// The frozen reference includes the previous checked public raw constructors.
#[path="r91_reference/field.rs"] mod reference;
use aspis_core::field::{M31,P};
fn main(){
    let hook=std::panic::take_hook();std::panic::set_hook(Box::new(|_|{}));
    let values=[0,1,2,3,(1<<30)-1,1<<30,(1<<30)+1,P-2,P-1,P,P+1,P+2,u32::MAX-1,u32::MAX];
    let mut raw=0;
    for a in values {for b in values {
        for op in 0..2 {
            let old=std::panic::catch_unwind(||if op==0{reference::M31(a).add(reference::M31(b)).0}else{reference::M31(a).sub(reference::M31(b)).0});
            let got=std::panic::catch_unwind(||if op==0{M31(a).add(M31(b)).0}else{M31(a).sub(M31(b)).0});
            match(got,old){(Ok(x),Ok(y))=>assert_eq!(x,y),(Err(_),Err(_))=>(),_=>panic!("raw behavior changed {a} {b} {op}")};raw+=1;
        }
    }}
    std::panic::set_hook(hook);
    let mut rng=0x918a_3366_2929_5544u64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(P))as u32};
    for _ in 0..265536 {
        let a=next();let b=next();
        let sum=M31(a).add(M31(b));let diff=M31(a).sub(M31(b));
        assert_eq!(sum.0,reference::M31(a).add(reference::M31(b)).0);
        assert_eq!(diff.0,reference::M31(a).sub(reference::M31(b)).0);
        assert_eq!(u64::from(sum.0),(u64::from(a)+u64::from(b))%u64::from(P));
        assert_eq!(u64::from(diff.0),(u64::from(a)+u64::from(P)-u64::from(b))%u64::from(P));
        assert!(sum.0<P && diff.0<P);
    }
    println!("R91_ADD canonical_pairs=265536 raw_operation_cases={raw} frozen_source=true independent_u64=true overflow_and_underflow_retained=true");
}
