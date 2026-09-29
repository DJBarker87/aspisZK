// Appended inside the actual query_arithmetic module in the host-only gate.
#[cfg(not(v8_performance_sbf))]
pub(super) fn r55_controls(){
    fn pack(values:&[u32])->Vec<u8>{
        let mut out=vec![0;values.len()*31/8];
        for(i,x)in values.iter().enumerate(){for bit in 0..31{if x&(1<<bit)!=0{let at=i*31+bit;out[at/8]|=1<<(at%8);}}}out
    }
    let p=corelib::field::P;
    let mut rng=0xd55a_2718_fedc_ba98u64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(p))as u32};
    let mut cases=0;
    for case in 0..512{
        let values:[u32;152]=core::array::from_fn(|i|match case{0=>0,1=>p-1,2..=153=>if i==case-2{p-1}else{0},_=>next()});
        let a=pack(&values[..104]);let b=pack(&values[104..]);
        let mut aa=[p;104];let mut bb=[p;48];
        assert_eq!(r55_decode_into(&a,&mut aa),Ok(()));assert_eq!(aa.as_slice(),&values[..104]);
        assert_eq!(r55_decode_into(&b,&mut bb),Ok(()));assert_eq!(bb.as_slice(),&values[104..]);
        for beta in [K::ZERO,K::ONE,K::ONE.neg(),K{c0:CM31::new(M31(next()),M31(next())),c1:CM31::new(M31(next()),M31(next()))}]{
            let gamma=K{c0:CM31::new(M31(next()),M31(next())),c1:CM31::new(M31(next()),M31(next()))};
            let powers=BetaCoefficients::new(gamma,beta);
            assert_eq!(combine_beta(&a,&b,&powers),r55_reference_combine_beta(&a,&b,&powers));cases+=1;
        }
    }
    let mut malformed=0;
    for beta in [K::ZERO,K::ONE,K::ONE.neg()]{
        let powers=BetaCoefficients::new(K::ONE,beta);
        for bad in 0..152{
            let mut values=[0;152];values[bad]=p;
            let a=pack(&values[..104]);let b=pack(&values[104..]);
            assert_eq!(combine_beta(&a,&b,&powers),Err(Error::Canonical));
            assert_eq!(combine_beta(&a,&b,&powers),r55_reference_combine_beta(&a,&b,&powers));malformed+=1;
        }
        for n in 0..=404{if n!=403{let a=vec![0;n];let b=vec![0;186];
            assert_eq!(combine_beta(&a,&b,&powers),Err(Error::Length));
            assert_eq!(combine_beta(&a,&b,&powers),r55_reference_combine_beta(&a,&b,&powers));malformed+=1;}}
        for n in 0..=187{if n!=186{let a=vec![0;403];let b=vec![0;n];
            assert_eq!(combine_beta(&a,&b,&powers),Err(Error::Length));
            assert_eq!(combine_beta(&a,&b,&powers),r55_reference_combine_beta(&a,&b,&powers));malformed+=1;}}
        // C1 canonicality precedes C2 length failure, even for beta=1.
        let mut values=[0;104];values[0]=p;let a=pack(&values);
        assert_eq!(combine_beta(&a,&[],&powers),Err(Error::Canonical));
        assert_eq!(combine_beta(&a,&[],&powers),r55_reference_combine_beta(&a,&[],&powers));malformed+=1;
    }
    let mut empty=[];
    assert_eq!(r55_decode_into::<0>(&[],&mut empty),Err(Error::Length));
    println!("R55_OPENING canonical_comparisons={cases} malformed_and_order={malformed} poisoned_output_cases=1024 beta_zero_one_retained=true all_152_limbs_checked=true source_reference=true");
}
