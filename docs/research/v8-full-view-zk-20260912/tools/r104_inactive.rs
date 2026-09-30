// Included after mechanically copied, source-pinned MASKS/IDS/ENDS/ROWS.
// Every ROWS slice is a distinct subset of 0..64. Thus total - subset is
// a nonnegative integer, and every sum is at most 64*(P-1) < 2^37.
use corelib::field::{M31,CM31,QM31 as K,P};
#[inline(never)]
pub(super) fn values(hb:&[K],out:&mut[K;19])->bool {
    if hb.len()<128{return false;}
    let mut totals=[[0u64;4];2];let mut invalid=0u32;
    for i in 0..128 {
        let v=hb[i];let raw=[v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0];
        for l in 0..4 {invalid|=raw[l]|raw[l].wrapping_add(1);totals[i/64][l]+=u64::from(raw[l]);}
    }
    if invalid>>31!=0{return false;}
    let one=|id:usize,channel:usize|{
        let mut sum=[0u64;4];
        for j in ENDS[id]..ENDS[id+1] {
            let v=hb[64*channel+ROWS[j]];
            sum[0]+=u64::from(v.c0.a.0);sum[1]+=u64::from(v.c0.b.0);
            sum[2]+=u64::from(v.c1.a.0);sum[3]+=u64::from(v.c1.b.0);
        }
        let limbs=core::array::from_fn::<_,4,_>(|l|M31::reduce_u64(totals[channel][l].wrapping_sub(sum[l])));
        K{c0:CM31::new(limbs[0],limbs[1]),c1:CM31::new(limbs[2],limbs[3])}
    };
    let shared:[K;12]=core::array::from_fn(|i|one(i,0));
    for low in 0..16 {out[low]=shared[IDS[low]];}
    for low in 0..3 {out[16+low]=one(IDS[low],1);}
    true
}
#[cfg(not(target_os="solana"))]
pub(super) fn controls(){
    let mut state=0x104b_1886_fd02_9181u64;
    let mut next=||{state^=state<<13;state^=state>>7;state^=state<<17;M31((state%u64::from(P))as u32)};
    for case in 0..4096 {
        let hb:[K;128]=core::array::from_fn(|i|{
            let v=core::array::from_fn::<_,4,_>(|j|if case==0{M31::ZERO}else if case==1{M31(P-1)}
                else if case<514{M31(if 4*i+j==case-2{P-1}else{0})}else{next()});
            K{c0:CM31::new(v[0],v[1]),c1:CM31::new(v[2],v[3])}
        });
        let mut out=[K::ONE;19];assert!(values(&hb,&mut out));
        for low in 0..19 {
            let l=if low<16{low}else{low-16};let offset=if low<16{0}else{64};
            let mut expected=K::ZERO;
            for group in 0..64{if MASKS[l]>>group&1!=0{expected=expected.add(hb[offset+group]);}}
            assert_eq!(out[low],expected,"case {case}, low {low}");
        }
    }
    for i in 0..128{for limb in 0..4{for bad in [P,P+1,u32::MAX]{
        let mut hb=[K::ZERO;128];let mut v=[0;4];v[limb]=bad;
        hb[i]=K{c0:CM31::new(M31(v[0]),M31(v[1])),c1:CM31::new(M31(v[2]),M31(v[3]))};
        let mut out=[K::ONE;19];assert!(!values(&hb,&mut out));assert_eq!(out,[K::ONE;19]);
    }}}
    println!("R104_INACTIVE profiles=4096 scalar_comparisons=77824 malformed=1536 all_coordinate_bases=true exact_integer_map=true");
}
