//! Research-only four-product affine channels, seeded before multiplication.
use super::*;
use corelib::field::QM31;
// Literal selected partial-channel reconstruction; QmCrossRange covers all u64.
#[inline]
fn reconstruct(sums:[[u64;3];3])->K{
        let f=|x:u64|(x&2147483647).wrapping_add(x>>31);
        let [[a,b,c],[d,e,fv],[g,h,i]]=sums.map(|row|row.map(f));
        let pad=68719476704u64;
        let r0=a.wrapping_add(d.wrapping_mul(3)).wrapping_add(pad)
            .wrapping_sub(b).wrapping_sub(e).wrapping_sub(fv);
        let r1=c.wrapping_add(fv.wrapping_mul(2)).wrapping_add(pad)
            .wrapping_sub(a).wrapping_sub(b).wrapping_sub(d).wrapping_sub(e.wrapping_mul(3));
        let r2=g.wrapping_add(b).wrapping_add(e).wrapping_add(pad)
            .wrapping_sub(h).wrapping_sub(a).wrapping_sub(d);
        let r3=i.wrapping_add(a).wrapping_add(b).wrapping_add(d).wrapping_add(e).wrapping_add(pad)
            .wrapping_sub(g).wrapping_sub(h).wrapping_sub(c).wrapping_sub(fv);
        return QM31{c0:CM31::new(M31::reduce_u64(r0),M31::reduce_u64(r1)),
            c1:CM31::new(M31::reduce_u64(r2),M31::reduce_u64(r3))};
}
#[cfg(test)]
fn reference_reconstruct(sums:[[u64;3];3])->K{
    let cm=|s:[u64;3]|{let [a,b,c]=s.map(M31::reduce_u64);CM31::new(a.sub(b),c.sub(a).sub(b))};
    let [a,b,c]=sums.map(cm);let rb=CM31::new(b.a.double().sub(b.b),b.a.add(b.b.double()));
    K{c0:a.add(rb),c1:c.sub(a).sub(b)}
}
type Channels=[[M31;3];3];
fn parts(v:K)->Channels{
    let s=v.c0.add(v.c1);
    [[v.c0.a,v.c0.b,v.c0.a.add(v.c0.b)],
     [v.c1.a,v.c1.b,v.c1.a.add(v.c1.b)],
     [s.a,s.b,s.a.add(s.b)]]
}
struct Prepared([Channels;4]);
impl Prepared{
    fn new(a:K)->Self{let a2=a.square();Self([a,a2,a2.mul(a),a2.square()].map(parts))}
    #[inline]
    fn affine<const N:usize>(&self,c:K,right:&[K;N])->K{
        assert!(N<=4);
        let [a,b,d,e]=[c.c0.a,c.c0.b,c.c1.a,c.c1.b].map(|x|u64::from(x.0));
        let ad=a.wrapping_add(d);
        let mut sums=[[a,0,a.wrapping_add(b)],[0;3],
            [ad,0,ad.wrapping_add(b.wrapping_add(e))]];
        for (left,right) in self.0.iter().zip(right){
            let right=parts(*right);
            for i in 0..3{for j in 0..3{
                // Canonical factors; every prefix <= n*(p-1)^2+4*(p-1), n<=4.
                sums[i][j]=sums[i][j].wrapping_add(u64::from(left[i][j].0).wrapping_mul(u64::from(right[i][j].0)));
            }}
        }
        reconstruct(sums)
    }
}
#[inline]
pub(super) fn evaluate(poly:&[K;28],a:K)->K{
    let powers=Prepared::new(a);let mut blocks=poly.chunks_exact(4).rev();
    let c=blocks.next().unwrap();let mut out=powers.affine(c[0],&[c[1],c[2],c[3]]);
    for c in blocks{out=powers.affine(c[0],&[c[1],c[2],c[3],out]);}
    out
}
#[cfg(test)]
mod tests{
    use super::*;
    #[test]
    fn seeded_four_products_and_degree27_match(){
        let mut rng=0x7365_6d61_6e74_6963u64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        let max=K{c0:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1)),c1:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1))};
        for case in 0..4096{
            let mut raw=core::array::from_fn(|_|core::array::from_fn(|_|{let _=m(&mut rng);rng}));
            if case==0{raw=[[0;3];3];}if case==1{raw=[[u64::MAX;3];3];}
            assert_eq!(reconstruct(raw),reference_reconstruct(raw));
        }
        for case in 0..4096{
            let mut l:[K;4]=core::array::from_fn(|_|k(&mut rng));let mut r:[K;4]=core::array::from_fn(|_|k(&mut rng));let mut c=k(&mut rng);
            if case==0{l=[K::ZERO;4];r=[K::ZERO;4];c=K::ZERO;}
            if case==1{l=[max;4];r=[max;4];c=max;}
            let prep=Prepared(l.map(parts));
            assert_eq!(prep.affine(c,&r),l.into_iter().zip(r).fold(c,|s,(a,b)|s.add(a.mul(b))));
            assert_eq!(prep.affine(c,&[r[0],r[1],r[2]]),(0..3).fold(c,|s,i|s.add(l[i].mul(r[i]))));
            assert_eq!(prep.affine(c,&[]),c);
        }
        for case in 0..1024{
            let mut p=core::array::from_fn(|_|k(&mut rng));let mut a=k(&mut rng);
            if case==0{p=[K::ZERO;28];a=K::ZERO;}if case==1{p=[max;28];a=max;}
            if case==2{a=K::ONE;}if case==3{a=K::ZERO;}
            assert_eq!(evaluate(&p,a),corelib::state_only_sumcheck::evaluate_state_only_polynomial(&p,a));
        }
        for i in 0..28{for a in [K::ZERO,K::ONE,sc(2),max]{let mut p=[K::ZERO;28];p[i]=K::ONE;
            assert_eq!(evaluate(&p,a),corelib::state_only_sumcheck::evaluate_state_only_polynomial(&p,a));}}
        // Literal worst prefix in a fresh u64 channel, independently of how
        // canonical additions restrict correlations between prepared lanes.
        let m=u64::from(corelib::field::P-1);let mut s=4*m;
        for n in 1..=4{s=s.wrapping_add(m.wrapping_mul(m));assert_eq!(u128::from(s),u128::from(4*m)+n*u128::from(m)*u128::from(m));}
        println!("SEMANTIC_CARRY arbitrary_affine=4096 degree27_profiles=1024 basis_cases=112 all_four_maximal_prefixes=true selected_reconstruction_raw_cases=4096");
    }
}
