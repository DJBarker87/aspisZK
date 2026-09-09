//! Fixed-size canonical compact-response reconstruction. Research only.
use super::*;
#[inline]
pub(super) fn missing(claim:K,c0:K,tail:&[K;26])->K {
    let mut sums=[0u64;4];
    for c in tail {
        let limbs=[c.c0.a,c.c0.b,c.c1.a,c.c1.b];
        for i in 0..4{sums[i]=sums[i].wrapping_add(u64::from(limbs[i].0));}
    }
    let claimed=[claim.c0.a,claim.c0.b,claim.c1.a,claim.c1.b];
    let zero=[c0.c0.a,c0.c0.b,c0.c1.a,c0.c1.b];
    let limbs:[M31;4]=core::array::from_fn(|i|M31::reduce_u64(
        u64::from(claimed[i].0).wrapping_add(60129542116)
        .wrapping_sub(u64::from(zero[i].0).wrapping_mul(2)).wrapping_sub(sums[i])));
    K{c0:CM31::new(limbs[0],limbs[1]),c1:CM31::new(limbs[2],limbs[3])}
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn arbitrary_compact_boundary_matches(){
        let mut rng=0x626f_756e_6461_7279u64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        let max=K{c0:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1)),c1:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1))};
        for case in 0..4096 {
            let mut claim=k(&mut rng);let mut c0=k(&mut rng);let mut tail=core::array::from_fn(|_|k(&mut rng));
            if case==0{claim=K::ZERO;c0=max;tail=[max;26];}
            if case==1{claim=max;c0=K::ZERO;tail=[K::ZERO;26];}
            if case==2{claim=K::ZERO;c0=K::ZERO;tail=[K::ZERO;26];}
            if case==3{claim=max;c0=max;tail=[max;26];}
            let actual=missing(claim,c0,&tail);
            let sum=tail.into_iter().fold(K::ZERO,|a,b|a.add(b));
            assert_eq!(actual,claim.sub(c0.add(c0).add(sum)));
            assert_eq!(c0.add(c0).add(actual).add(sum),claim);
        }
        for index in 0..26 {for lane in 0..4 {
            let mut tail=[K::ZERO;26];let mut v=[M31::ZERO;4];v[lane]=M31(corelib::field::P-1);
            tail[index]=K{c0:CM31::new(v[0],v[1]),c1:CM31::new(v[2],v[3])};
            assert_eq!(missing(K::ONE,K::ZERO,&tail),K::ONE.sub(tail[index]));
        }}
        println!("SEMANTIC_BOUNDARY arbitrary=4096 basis_cells=104 all_maximum_and_zero_edges=true literal_boundary=true");
    }
}
