// Included inside the actual staged fast-G module, host controls only.
#[cfg(not(performance_sbf))]
pub(super) fn check_cyclic() {
    for position in 0..271 {
        for limb in 0..4 {
            let mut coins=[K::ZERO;271]; let mut limbs=[M31::ZERO;4];
            limbs[limb]=M31::ONE;
            coins[position]=K{c0:CM31::new(limbs[0],limbs[1]),c1:CM31::new(limbs[2],limbs[3])};
            let mut old=[K::ZERO;1024]; let mut got=[K::ZERO;1024];
            apply_2048_reference(&coins,&mut old); apply(&coins,&mut got);
            assert_eq!(got,old,"basis position {position}, limb {limb}");
            let mut power=M31::ONE;
            for j in 0..1024 {
                assert_eq!(got[j],coins[position].mul_m31(power));
                power=power.mul(M31((position+1) as u32));
            }
        }
    }
    for case in 0..32u32 {
        let coins=core::array::from_fn(|i| {
            let a=if case==0 {0}else if case==1 {2147483646}else{i as u32*97+case*83};
            let b=case*17+i as u32*29;
            K{c0:CM31::new(M31(a),M31(b)),c1:CM31::new(M31((a+case)%2147483647),M31(b+3*i as u32))}
        });
        let mut old=[K::ZERO;1024]; let mut got=[K::ZERO;1024];
        apply_2048_reference(&coins,&mut old); apply(&coins,&mut got);
        assert_eq!(got,old,"vector {case}");
        let mut powers=[M31::ONE;271];
        for j in 0..1024 {
            let mut expected=K::ZERO;
            for i in 0..271 {
                expected=expected.add(coins[i].mul_m31(powers[i]));
                powers[i]=powers[i].mul(M31((i+1) as u32));
            }
            assert_eq!(got[j],expected,"direct vector {case}, output {j}");
        }
        let dirty=K{c0:CM31::new(M31(3),M31(5)),c1:CM31::new(M31(7),M31(11))};
        let mut dirty_out=[dirty;1024]; apply(&coins,&mut dirty_out);
        assert_eq!(dirty_out,got);
    }
    assert_eq!(ROOTS[2].pow(1024),CM31::ONE);
    assert_ne!(ROOTS[2].pow(512),CM31::ONE);
    for i in 0..271 {
        let a=M31((i+1) as u32);
        assert_eq!(COIN_SCALE_1024[i],M31::ONE.sub(a.pow(1024)));
        if i==0 {
            assert_eq!(COIN_SCALE_1024[i],M31::ZERO);
            assert_eq!(DC_WEIGHT_1024[i],M31(1024));
        } else {
            assert_ne!(COIN_SCALE_1024[i],M31::ZERO);
            assert_eq!(DC_WEIGHT_1024[i].mul(M31::ONE.sub(a)),COIN_SCALE_1024[i]);
        }
    }
    for i in 0..1024 {
        let w=ROOTS[2*i]; let mut d=CM31::ONE;
        for a in 1..=271 {d=d.mul(CM31::ONE.sub(w.mul_m31(M31(a))));}
        if i==0 {assert_eq!(d,CM31::ZERO);assert_eq!(INV_DEN_1024[i],CM31::ZERO);}
        else {assert_ne!(d,CM31::ZERO);assert_eq!(d.mul(INV_DEN_1024[i]),CM31::ONE);}
    }
    // Actual malformed algorithms: unnormalized old circular convolution,
    // and normalized new convolution with its DC replacement omitted.
    let mut coins=[K::ZERO;271]; coins[0]=K::ONE; coins[1]=K::ONE;
    let mut expected=[K::ZERO;1024];apply(&coins,&mut expected);
    let mut numerator=[K::ZERO;1024];let mut work=vec![CM31::ZERO;1024];
    numerator_into(&coins,&mut numerator,&mut work);
    work.fill(CM31::ZERO);
    for i in 0..271 {work[i]=numerator[i].c0;}
    fft(&mut work,false);
    for i in 0..1024 {work[i]=work[i].mul(INVERSE_SPECTRUM[2*i]);}
    fft(&mut work,true);
    assert!((0..1024).any(|j|work[j]!=expected[j].c0),"naive old circular wrap must fail");
    cyclic_numerator_into(&coins,&mut numerator,&mut work);
    work.fill(CM31::ZERO);
    for i in 0..271 {work[i]=numerator[i].c0;}
    fft(&mut work,false); work[0]=CM31::ZERO;
    for i in 1..1024 {work[i]=work[i].mul(INV_DEN_1024[i]);}
    fft(&mut work,true);
    assert!((0..1024).any(|j|work[j]!=expected[j].c0),"omitted DC replacement must fail");
    println!("PASS: cyclic 1084 four-limb basis cases, 32 full QM31 three-way/dirty vectors, 271 scale/DC constants, 1024 denominator identities and two malformed-algorithm controls");
}
