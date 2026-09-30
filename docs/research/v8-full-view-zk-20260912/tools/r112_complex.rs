// Keep already-canonical folded weights private through the final complex
// norm multiplication. No new unchecked Q constructor is exposed.
impl Q {
    #[inline(always)]
    pub fn mul_complex(self,re:u32,im:u32)->Option<Self> {
        if re>=P || im>=P{return None;}
        let [a,b,c,d]=self.0.map(u64::from);let e=u64::from(re);let f=u64::from(im);
        const PP:u64=(P as u64)*(P as u64);
        // Each sum/difference is nonnegative and <2*P^2 <2^63.
        Some(Self([reduce((a*e).wrapping_add(PP).wrapping_sub(b*f)),
            reduce((a*f).wrapping_add(b*e)),
            reduce((c*e).wrapping_add(PP).wrapping_sub(d*f)),
            reduce((c*f).wrapping_add(d*e))]))
    }
}
#[cfg(not(target_os="solana"))]
pub fn r112_controls(){
    use corelib::field::{M31,CM31,QM31 as K};let mut rng=0x112cead928317u64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(P))as u32};
    let k=|v:[u32;4]|K{c0:CM31::new(M31(v[0]),M31(v[1])),c1:CM31::new(M31(v[2]),M31(v[3]))};
    for case in 0..69632 {
        let mut v:[u32;6]=core::array::from_fn(|_|next());
        if case<4096{let vals=[0,1,P-2,P-1];let mut c=case;for x in &mut v{*x=vals[c%4];c/=4;}}
        let limbs=v[..4].try_into().unwrap();let a=k(limbs);let b=CM31::new(M31(v[4]),M31(v[5]));
        let q=Q::from_limbs(limbs).unwrap().mul_complex(v[4],v[5]).unwrap();
        assert_eq!(k(q.limbs()),K{c0:a.c0.mul(b),c1:a.c1.mul(b)});assert!(q.limbs().iter().all(|x|*x<P));
    }
    for bad in [P,P+1,u32::MAX]{assert_eq!(Q::ZERO.mul_complex(bad,0),None);assert_eq!(Q::ZERO.mul_complex(0,bad),None);}
    println!("R112_COMPLEX comparisons=69632 boundary_cartesian_cases=4096 malformed=6 closure_canonical=true");
}
