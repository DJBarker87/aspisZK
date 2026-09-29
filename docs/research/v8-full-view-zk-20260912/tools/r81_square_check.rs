// Actual candidate square versus the frozen control and independent u128.
#[path="r81_reference/field.rs"] mod reference;
use aspis_core::field::{QM31 as K,CM31,M31,P};
use aspis_core::field as f;
fn mk(v:[u32;4])->K{K{c0:CM31::new(M31(v[0]),M31(v[1])),c1:CM31::new(M31(v[2]),M31(v[3]))}}
fn old(v:[u32;4])->reference::QM31{reference::QM31{
    c0:reference::CM31::new(reference::M31(v[0]),reference::M31(v[1])),
    c1:reference::CM31::new(reference::M31(v[2]),reference::M31(v[3]))}}
fn encode(k:K)->[u8;16]{let mut b=[0;16];k.write_le_bytes(&mut b);b}
fn old_bytes(k:reference::QM31)->[u8;16]{let mut b=[0;16];k.write_le_bytes(&mut b);b}
fn independent(v:[u32;4])->K{
    let [a,b,c,d]=v.map(u128::from);let p=u128::from(P);let pp=p*p;
    mk([a*a+2*c*c+4*pp-b*b-2*d*d-2*c*d,
        2*a*b+c*c+4*c*d+pp-d*d,
        2*a*c+2*pp-2*b*d,2*a*d+2*b*c].map(|x|(x%p)as u32))
}
fn main(){
    let mut rng=0x8181_2929_2211_5544u64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(P))as u32};
    for case in 0..265536 {
        let mut v=core::array::from_fn(|_|next());
        if case<65536 {let values=[0,1,2,3,7,31,63,255,65535,1<<28,1<<29,1<<30,P-4,P-3,P-2,P-1];
            let mut k=case;for x in &mut v{*x=values[k%16];k/=16;}}
        let actual=mk(v).square();
        assert_eq!(actual,independent(v));
        assert_eq!(actual,mk(v).mul(mk(v)));
        assert_eq!(encode(actual),old_bytes(old(v).square()));
        if case<8192 {
            let left=[mk(v),mk(core::array::from_fn(|_|next())),mk(core::array::from_fn(|_|next())),mk(core::array::from_fn(|_|next()))];
            let right=core::array::from_fn::<_,4,_>(|_|mk(core::array::from_fn(|_|next())));
            let constant=mk(core::array::from_fn(|_|next()));
            let model=|n| (0..n).fold(K::ZERO,|s,i|s.add(left[i].mul(right[i])));
            assert_eq!(f::qm31_sum_products2([left[0],left[1]],[right[0],right[1]]),model(2));
            assert_eq!(f::qm31_sum_products3([left[0],left[1],left[2]],[right[0],right[1],right[2]]),model(3));
            assert_eq!(f::qm31_sum_products4(left,right),model(4));
            let prepared=left.map(f::PreparedQm31Multiplier::new);
            assert_eq!(f::qm31_sum_products2_prepared(&[prepared[0],prepared[1]],&[right[0],right[1]]),model(2));
            assert_eq!(f::qm31_sum_products3_prepared(&[prepared[0],prepared[1],prepared[2]],&[right[0],right[1],right[2]]),model(3));
            assert_eq!(f::qm31_add_sum_products3_prepared(constant,&[prepared[0],prepared[1],prepared[2]],&[right[0],right[1],right[2]]),constant.add(model(3)));
        }
    }
    let hook=std::panic::take_hook();std::panic::set_hook(Box::new(|_|{}));
    let mut invalid=0;
    for lane in 0..4{for bad in [P,P+1,P+2,u32::MAX-1,u32::MAX]{
        for other in [0,1,P-1]{let mut v=[other;4];v[lane]=bad;
            let actual=std::panic::catch_unwind(||encode(mk(v).square()));
            let expect=std::panic::catch_unwind(||old_bytes(old(v).square()));
            match(actual,expect){(Ok(a),Ok(b))=>assert_eq!(a,b),(Err(_),Err(_))=>(),_=>panic!("fallback changed")}
            let actual=std::panic::catch_unwind(||encode(f::qm31_sum_products3([mk(v);3],[K::ONE;3])));
            let expect=std::panic::catch_unwind(||old_bytes(reference::qm31_sum_products3([old(v);3],[reference::QM31::ONE;3])));
            match(actual,expect){(Ok(a),Ok(b))=>assert_eq!(a,b),(Err(_),Err(_))=>(),_=>panic!("dot fallback changed")}
            let actual=std::panic::catch_unwind(||encode(f::qm31_add_sum_products3_prepared(mk(v),&[f::PreparedQm31Multiplier::new(K::ONE);3],&[K::ONE;3])));
            let expect=std::panic::catch_unwind(||old_bytes(reference::qm31_add_sum_products3_prepared(old(v),&[reference::PreparedQm31Multiplier::new(reference::QM31::ONE);3],&[reference::QM31::ONE;3])));
            match(actual,expect){(Ok(a),Ok(b))=>assert_eq!(a,b),(Err(_),Err(_))=>(),_=>panic!("affine fallback changed")}
            invalid+=1;
        }
    }}
    std::panic::set_hook(hook);
    println!("R81_SQUARE canonical=265536 boundary=65536 random=200000 invalid={invalid} short_dot_comparisons=49152 frozen_source=true independent_u128=true fallback_retained=true");
}
