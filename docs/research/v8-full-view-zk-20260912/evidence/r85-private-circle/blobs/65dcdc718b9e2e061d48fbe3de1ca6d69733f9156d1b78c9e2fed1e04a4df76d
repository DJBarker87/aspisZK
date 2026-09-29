//! Expanded normalized butterfly, using the retained checked three-product sum.
use super::*;
use corelib::field::{PreparedQm31Multiplier as P,qm31_sum_products3_prepared};
pub(super) struct Prepared([P;3]);
impl Prepared{
    pub(super) fn new(a:K)->Self{let a2=a.square();Self([P::new(a),P::new(a2),P::new(a2.mul(a))])}
    #[inline]
    pub(super) fn fold(&self,v:[K;4],ix:M31,iy:M31)->K{
        let a=v[0].add(v[1]);let b=v[2].add(v[3]);
        let c=v[0].sub(v[1]);let d=v[2].sub(v[3]);
        let terms=[c.sub(d).mul_m31(iy.half()),a.sub(b).mul_m31(ix.half()),
            c.add(d).mul_m31(ix.mul(iy))];
        a.add(b).half().half().add(qm31_sum_products3_prepared(&self.0,&terms))
    }
}
#[cfg(test)]
mod tests{
    use super::*;
    #[test]
    fn expanded_matches_sequential_on_arbitrary_inputs(){
        let mut rng=0x666f_6c64_2d76_3821u64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        for case in 0..4096{
            let mut v=core::array::from_fn(|_|k(&mut rng));let mut a=k(&mut rng);
            let mut ix=m(&mut rng);let mut iy=m(&mut rng);
            if case<16{a=if case%2==0{K::ZERO}else{K::ONE};ix=M31((case/2)%2);iy=M31((case/4)%2);}
            if case==16{v=[K::ZERO;4];}if case==17{v=[K{c0:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1)),c1:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1))};4];}
            assert_eq!(Prepared::new(a).fold(v,ix,iy),corelib::field::qm31_circle_to_line_fold4(v,a,ix,iy));
        }
        for slot in 0..4{for a in [K::ZERO,K::ONE,sc(2),sc(corelib::field::P-1)]{
            let mut v=[K::ZERO;4];v[slot]=K::ONE;
            assert_eq!(Prepared::new(a).fold(v,M31(7),M31(13)),corelib::field::qm31_circle_to_line_fold4(v,a,M31(7),M31(13)));
        }}
        println!("QUOTIENT_FOLD arbitrary_profiles=4096 slot_basis_cases=16 zero_challenges_and_coordinates=true");
    }
}
