// Included inside quotient_fold. Validate once and remain in private Q across
// subtraction, quotient products and the complete four-slot fold. No inverse,
// parser, domain or authentication check moves here or disappears.
#[path="r81_canonical_basis.rs"] mod r85_private;
use r85_private::Q as CQ;
fn r85_in(v:K)->Option<CQ> {CQ::from_limbs([v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0])}
fn r85_out(v:CQ)->K {let [a,b,c,d]=v.limbs();K{c0:CM31::new(M31(a),M31(b)),c1:CM31::new(M31(c),M31(d))}}
pub(super) struct Canonical {powers:[CQ;3],iv:[CQ;2]}
impl Canonical {
    pub(super) fn new(alpha:K,iv:[K;2])->Option<Self> {
        let a=r85_in(alpha)?;let a2=a.square();
        Some(Self{powers:[a,a2,a2.mul(a)],iv:[r85_in(iv[0])?,r85_in(iv[1])?]})
    }
    #[inline(never)]
    pub(super) fn divided(&self,all:[K;4],inverse:[K;4],h:M31,use_x:bool,ix:M31,iy:M31)->Option<K> {
        let mut v=[CQ::ZERO;4];
        let delta=self.iv[1].mul_m31(h.0)?;
        for slot in 0..4 {
            let same=if use_x {slot<2}else{slot==0||slot==3};
            let point=self.iv[0].add(if same{delta}else{delta.neg()});
            v[slot]=r85_in(all[slot])?.sub(point).mul(r85_in(inverse[slot])?);
        }
        // Validate arbitrary API inputs, even though Selected supplies these
        // two canonical scalars in the actual verifier.
        if ix.0>=corelib::field::P || iy.0>=corelib::field::P {return None;}
        let a=v[0].add(v[1]);let b=v[2].add(v[3]);
        let c=v[0].sub(v[1]);let d=v[2].sub(v[3]);
        let terms=[c.sub(d).mul_m31(ix_half(iy))?,a.sub(b).mul_m31(ix_half(ix))?,
            c.add(d).mul_m31(ix.mul(iy).0)?];
        Some(r85_out(a.add(b).half().half().add(CQ::dot(self.powers,terms))))
    }
}
#[inline(always)] fn ix_half(v:M31)->u32 {(v.0>>1)|((v.0&1)<<30)}

#[cfg(not(target_os="solana"))]
pub(super) fn r85_controls() {
    let mut rng=0x850123abcd776655u64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(corelib::field::P))as u32};
    let mut count=0;
    for case in 0..4096 {
        let x:[K;15]=core::array::from_fn(|i| {
            let mut m=||M31(if case==0{0}else if case==1{corelib::field::P-1}else{next()});
            let v=K{c0:CM31::new(m(),m()),c1:CM31::new(m(),m())};
            if case<17&&i==0 {if case%2==0{K::ZERO}else{K::ONE}}else{v}
        });
        let alpha=x[0];let iv=[x[1],x[2]];let all:[K;4]=x[3..7].try_into().unwrap();
        let inv:[K;4]=x[7..11].try_into().unwrap();let h=M31(next());let ix=M31(next());let iy=M31(next());
        let new=Canonical::new(alpha,iv).unwrap();
        for use_x in [false,true] {
            let q=core::array::from_fn(|slot| {
                let delta=iv[1].mul_m31(h);let same=if use_x{slot<2}else{slot==0||slot==3};
                all[slot].sub(iv[0].add(if same{delta}else{delta.neg()})).mul(inv[slot])
            });
            assert_eq!(new.divided(all,inv,h,use_x,ix,iy),Some(corelib::field::qm31_circle_to_line_fold4(q,alpha,ix,iy)));
            count+=1;
        }
        let l=core::array::from_fn(|i|r85_in(x[i]).unwrap());
        let r=core::array::from_fn(|i|r85_in(x[i+4]).unwrap());
        assert_eq!(r85_out(CQ::dot::<4>(l,r)),corelib::field::qm31_sum_products4(x[..4].try_into().unwrap(),x[4..8].try_into().unwrap()));
    }
    // All public kernel boundaries reject noncanonical raw words; verifier
    // fallback behavior is retained by the caller, not silently normalized.
    let new=Canonical::new(K::ONE,[K::ONE;2]).unwrap();let mut bad=0;
    for limb in 0..4 {for raw in [corelib::field::P,corelib::field::P+1,u32::MAX] {
        let mut x=[0;4];x[limb]=raw;let v=K{c0:CM31::new(M31(x[0]),M31(x[1])),c1:CM31::new(M31(x[2]),M31(x[3]))};
        assert!(Canonical::new(v,[K::ONE;2]).is_none());
        for slot in 0..4 {let mut a=[K::ZERO;4];a[slot]=v;
            assert_eq!(new.divided(a,[K::ONE;4],M31::ONE,true,M31::ONE,M31::ONE),None);
            assert_eq!(new.divided([K::ZERO;4],a,M31::ONE,true,M31::ONE,M31::ONE),None);bad+=2;
        }
    }}
    println!("R85_QUOTIENT arbitrary_full_kernel_comparisons={count} private_dots=4096 malformed_array_boundaries={bad} domain_checks_outside_unchanged=true");
}
