// Actual selected mixed-width kernel against an independent u128 sum.
// Host only: arbitrary canonical matrices, not just honest gamma powers.
#[cfg(not(v8_performance_sbf))]
pub(super) fn r61_controls(){
    fn pack(v:&[u32])->Vec<u8>{
        let mut b=vec![0;v.len()*31/8];
        for (i,x) in v.iter().enumerate(){for bit in 0..31{if x&(1<<bit)!=0{let at=i*31+bit;b[at/8]|=1<<(at%8);}}}b
    }
    let p=corelib::field::P;
    let mut rng=0x61ab_7823_9182_fed1u64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(p)) as u32};
    let mut scalar=0;let mut packed=0;
    for case in 0..4096{
        let mut values:[u32;26]=core::array::from_fn(|_|next());
        let mut weights:[[u32;4];26]=core::array::from_fn(|_|core::array::from_fn(|_|next()));
        if case==0{values=[0;26];weights=[[0;4];26];}
        if case==1{values=[p-1;26];weights=[[p-1;4];26];}
        if (2..28).contains(&case){values=[0;26];values[case-2]=p-1;}
        if (28..132).contains(&case){weights=[[0;4];26];weights[(case-28)/4][(case-28)%4]=p-1;}
        let expected:[M31;4]=core::array::from_fn(|l|M31(((0..26).map(|i|u128::from(values[i])*u128::from(weights[i][l])).sum::<u128>()%u128::from(p))as u32));
        let actual=[fixed_dot::<0>(&values,&weights),fixed_dot::<1>(&values,&weights),fixed_dot::<2>(&values,&weights),fixed_dot::<3>(&values,&weights)];
        assert_eq!(actual,expected);scalar+=4;
        let mut coefficients=BetaCoefficients::new(K::ONE,K::ZERO);
        coefficients.c1_limbs=weights;
        let c1:[u32;104]=core::array::from_fn(|i|values[i%26]);
        let encoded=pack(&c1);
        let result=combine_beta(&encoded,&[0;186],&coefficients).unwrap();
        let wanted=K{c0:CM31::new(expected[0],expected[1]),c1:CM31::new(expected[2],expected[3])};
        assert_eq!(result,[wanted;4]);packed+=1;
    }
    controls();
    println!("R61_OPENING scalar_u128_comparisons={scalar} packed_arbitrary_matrices={packed} canonical_max=true all_basis_positions=true");
}
