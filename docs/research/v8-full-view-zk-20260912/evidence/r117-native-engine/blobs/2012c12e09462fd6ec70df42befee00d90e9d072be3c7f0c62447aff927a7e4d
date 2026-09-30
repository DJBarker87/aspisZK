const R58_TAG_BASE:u32=1_124_073_472;
const _:()={
    let mut i=0;
    while i<constants::COPY_LINKS.len(){
        assert!(constants::COPY_LINKS[i].tag==R58_TAG_BASE+i as u32);i+=1;
    }
    assert!(constants::COPY_LINKS.len()==136);
    i=0;
    while i<272 {assert!(COPY_TAG_TERMS.1[i]>=R58_TAG_BASE && COPY_TAG_TERMS.1[i]-R58_TAG_BASE<=135);i+=1;}
};

#[inline(never)]
fn r58_tag_delta(coordinate:usize,selectors:&Selectors)->QM31{
    let mut raw=[0u64;4];
    let mut index=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate]);
    let end=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate+1]);
    while index<end {
        let value=selectors.high[usize::from(COPY_TAG_TERMS.0[index])];
        let tag=u64::from(COPY_TAG_TERMS.1[index].wrapping_sub(R58_TAG_BASE));
        // Static registry bounds: <=272 products of u32 limbs and tags <=135.
        // Every product/sum prefix is below 2^48, hence below u64::MAX.
        raw[0]=raw[0].wrapping_add(u64::from(value.c0.a.0)*tag);
        raw[1]=raw[1].wrapping_add(u64::from(value.c0.b.0)*tag);
        raw[2]=raw[2].wrapping_add(u64::from(value.c1.a.0)*tag);
        raw[3]=raw[3].wrapping_add(u64::from(value.c1.b.0)*tag);
        index+=1;
    }
    QM31{c0:CM31::new(M31::reduce_u64(raw[0]),M31::reduce_u64(raw[1])),
        c1:CM31::new(M31::reduce_u64(raw[2]),M31::reduce_u64(raw[3]))}
}

#[cfg(not(v8_performance_sbf))]
pub fn r58_tag_controls()->(usize,usize,usize){
    let mut seed=0x5899_3481_774a_7295u64;
    let mut sample=||{let mut word=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;M31((seed%u64::from(aspis_core::field::P))as u32)};
        QM31{c0:CM31::new(word(),word()),c1:CM31::new(word(),word())}};
    let mut tags=0;let mut finishes=0;let mut negatives=0;
    for case in 0..320{
        let mut high=core::array::from_fn(|_|sample());let low=core::array::from_fn(|_|sample());
        if case<256{
            high.fill(QM31::ZERO);let v=&mut high[case/4];match case%4{
                0=>v.c0.a=M31::ONE,1=>v.c0.b=M31::ONE,2=>v.c1.a=M31::ONE,_=>v.c1.b=M31::ONE}
        }
        if case==256{high.fill(QM31::ZERO);}
        if case==257{let v=M31(aspis_core::field::P-1);high.fill(QM31{c0:CM31::new(v,v),c1:CM31::new(v,v)});}
        let selectors=Selectors{high,low};
        for coordinate in 0..30{
            let mut total=QM31::ZERO;
            for i in usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate])..usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate+1]){
                total=total.add(selectors.high[usize::from(COPY_TAG_TERMS.0[i])]);
            }
            let delta=r58_tag_delta(coordinate,&selectors);
            let original=r58_reference_tag_dot(coordinate,&selectors);
            assert_eq!(delta.add(total.mul_m31(M31(R58_TAG_BASE))),original);
            if delta!=original{negatives+=1;}tags+=1;
        }
        let patterns=core::array::from_fn(|_|sample());
        for variant in [PoolV1PairForestCompiledVariantV1::PrivateTransfer,PoolV1PairForestCompiledVariantV1::Withdrawal]{
            let mut scratch=vec![QM31::ZERO;103];
            r57_gather(&mut scratch,&selectors,0xd556_9921_bfaf_e746^case as u64,variant);
            assert_eq!(finish_selector_tensor_basis(&scratch,&patterns,&selectors),
                r58_reference_finish(&scratch,&patterns,&selectors));finishes+=1;
        }
    }
    assert!(negatives>0);
    (tags,finishes,negatives)
}
