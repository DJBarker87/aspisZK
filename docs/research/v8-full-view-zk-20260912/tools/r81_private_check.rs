#[cfg(not(target_os="solana"))]
pub fn r81_private_kernel_check(){
    use r81_canonical::Q;
    let mut rng=0x33aa_7711_5566_99ccu64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(P))as u32};
    let old=|v:[u32;4]|K{c0:aspis_core::field::CM31::new(M31(v[0]),M31(v[1])),c1:aspis_core::field::CM31::new(M31(v[2]),M31(v[3]))};
    for case in 0..265536 {
        let mut raw:[u32;8]=core::array::from_fn(|_|next());
        if case<65536 {let values=[0,1,P-2,P-1];let mut n=case;for v in &mut raw{*v=values[n%4];n/=4;}}
        let a:[u32;4]=raw[..4].try_into().unwrap();let b:[u32;4]=raw[4..].try_into().unwrap();
        let x=Q::from_limbs(a).unwrap();let y=Q::from_limbs(b).unwrap();
        for (actual,expected) in [(x.mul(y),old(a).mul(old(b))),(x.add(y),old(a).add(old(b))),(x.sub(y),old(a).sub(old(b)))] {
            assert_eq!(old(actual.limbs()),expected);
            assert!(actual.limbs().iter().all(|&v|v<P));
        }
    }
    for lane in 0..4{for bad in [P,P+1,u32::MAX]{let mut v=[0;4];v[lane]=bad;assert_eq!(Q::from_limbs(v),None);}}
    println!("R81_PRIVATE canonical_pairs=265536 operation_comparisons=796608 rejected_constructors=12 closure_canonical=true");
}
