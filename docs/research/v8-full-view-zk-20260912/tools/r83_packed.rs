// Four canonical matrix columns for multiplication by an arbitrary QM31.
// This is public coefficient preparation, not a change to the packed wire.
fn r83_matrix(v:K)->[[u32;4];4] {
    let (a,b,c,d)=(v.c0.a,v.c0.b,v.c1.a,v.c1.b);
    let x=c.double().sub(d);let y=c.add(d.double());
    [[a.0,b.0,c.0,d.0],[b.neg().0,a.0,d.neg().0,c.0],
        [x.0,y.0,a.0,b.0],[y.neg().0,x.0,b.neg().0,a.0]]
}
#[inline(always)]
fn r83_mixed_limb<const L:usize>(c1:&[u32;26],c2:&[u32;48],slot:usize,p:&BetaCoefficients)->M31 {
    macro_rules! value {($i:expr)=>{{
        const I:usize=$i;
        u64::from(if I<26 {c1[I]}else{let j=I.wrapping_sub(26);c2[16*(j/4)+4*slot+j%4]})
    }}}
    macro_rules! weight {($i:expr)=>{{
        const I:usize=$i;
        u64::from(if I<26 {p.c1_limbs[I][L]}else{p.mixed[I.wrapping_sub(26)][L]})
    }}}
    macro_rules! chunk {($i:expr)=>{reduce_chunk((value!($i)*weight!($i))
        .wrapping_add(value!($i+1)*weight!($i+1))
        .wrapping_add(value!($i+2)*weight!($i+2))
        .wrapping_add(value!($i+3)*weight!($i+3)))}}
    // Nine four-product chunks plus two terms: <=50P<2^37 after the
    // retained partial fold. Each individual chunk fits in u64.
    let sum=chunk!(0).wrapping_add(chunk!(4)).wrapping_add(chunk!(8))
        .wrapping_add(chunk!(12)).wrapping_add(chunk!(16)).wrapping_add(chunk!(20))
        .wrapping_add(chunk!(24)).wrapping_add(chunk!(28)).wrapping_add(chunk!(32))
        .wrapping_add(reduce_chunk((value!(36)*weight!(36)).wrapping_add(value!(37)*weight!(37))));
    M31::reduce_u64(sum)
}

#[cfg(not(v8_performance_sbf))]
pub(super) fn r83_packed_controls(){
    fn pack(v:&[u32])->Vec<u8>{
        let mut b=vec![0;v.len()*31/8];
        for (i,x) in v.iter().enumerate(){for bit in 0..31{if x&(1<<bit)!=0{let at=31*i+bit;b[at/8]|=1<<(at%8);}}}b
    }
    let p=corelib::field::P;let mut rng=0x83ab_a232_ddff_7788u64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(p)) as u32};
    for case in 0..4096 {
        let values:[u32;152]=core::array::from_fn(|i|if case==0{0}else if case==1{p-1}
            else if case<154{if i==case-2{p-1}else{0}}else{next()});
        let mut coeff=BetaCoefficients::new(K::ONE,K::ZERO);
        coeff.c1_limbs=core::array::from_fn(|_|core::array::from_fn(|_|if case==1{p-1}else{next()}));
        let raw:[K;3]=core::array::from_fn(|_|{
            let mut m=||M31(if case==1{p-1}else{next()});
            K{c0:CM31::new(m(),m()),c1:CM31::new(m(),m())}
        });
        coeff.helpers=raw.map(corelib::field::PreparedQm31Multiplier::new);
        let columns=raw.map(r83_matrix);
        coeff.mixed=core::array::from_fn(|i|columns[i/4][i%4]);
        let c1=pack(&values[..104]);let c2=pack(&values[104..]);
        assert_eq!(combine_beta(&c1,&c2,&coeff),r55_reference_combine_beta(&c1,&c2,&coeff),
            "arbitrary mixed coefficients case {case}");
    }
    println!("R83_PACKED arbitrary_coefficient_profiles=4096 all_152_basis_positions=true maximal_canonical=true old_reference_retained=true");
}
