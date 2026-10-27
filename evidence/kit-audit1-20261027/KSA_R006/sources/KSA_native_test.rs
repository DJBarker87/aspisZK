
#[cfg(test)]
mod KSA_diagnostic {
    extern crate std;
    use super::field::{CM31,M31,QM31,WideExact,P};
    fn q(n:u32)->QM31 { QM31 { c0:CM31::new(M31(n),M31::ZERO),c1:CM31::ZERO } }
    // Literal control flow of XRn_Join_qpow, using frozen native multiplication.
    fn kit_pow(x:QM31,e:u128)->QM31 {
        if e==0 {return QM31::ONE;}
        let n=e-1; let y=kit_pow(x,n/2); let z=y.mul(y);
        if n%2==0 {z.mul(x)} else {z}
    }
    fn ka(a:M31,b:M31)->M31 { let s=a.0.wrapping_add(b.0);M31(if s>=P {s-P}else{s}) }
    fn ks(a:M31,b:M31)->M31 { let s=a.0.wrapping_add(P).wrapping_sub(b.0);M31(if s>=P{s-P}else{s}) }
    fn ca(x:CM31,y:CM31)->CM31 {CM31::new(ka(x.a,y.a),ka(x.b,y.b))}
    fn cs(x:CM31,y:CM31)->CM31 {CM31::new(ks(x.a,y.a),ks(x.b,y.b))}
    fn cm(x:CM31,y:CM31)->CM31 {
        let m0=x.a.mul(y.a);let m1=x.b.mul(y.b);
        let m2=M31::reduce_u64((u64::from(x.a.0)+u64::from(x.b.0))*(u64::from(y.a.0)+u64::from(y.b.0)));
        CM31::new(ks(m0,m1),ks(ks(m2,m0),m1))
    }
    fn km(x:QM31,y:QM31)->QM31 {
        let m0=cm(x.c0,y.c0);let m1=cm(x.c1,y.c1);
        let m2=cm(ca(x.c0,x.c1),ca(y.c0,y.c1));
        let r=CM31::new(ks(ka(m1.a,m1.a),m1.b),ka(m1.a,ka(m1.b,m1.b)));
        QM31{c0:ca(m0,r),c1:cs(cs(m2,m0),m1)}
    }
    #[test]
    fn KSA_frozen_differential() {
        std::println!("KSA inv2 native={} kit=2",M31(2).inv().0);
        assert_eq!(M31(2).inv().0,1073741824);
        assert_eq!(kit_pow(q(2),2),QM31::ONE);
        assert_ne!(kit_pow(q(2),2),q(2).mul(q(2)));
        for n in [0,1,2,P-1,P,u32::MAX] {
            let bs=n.to_le_bytes();
            let native=M31::from_le_bytes(bs);
            let model=if n<P {Some(M31(n))} else {None};
            assert_eq!(native,model);std::println!("KSA m31 bytes {} {:?}",n,native);
        }
        for n in [0,1,2,P-1] {
            let x=WideExact::from_qm31(q(n));
            let bs=x.to_le_bytes();assert_eq!(WideExact::from_le_bytes(&bs),Some(x));
            assert_eq!(WideExact::from_limbs(x.to_limbs()),Some(x));
            assert_eq!(x.mul_m31(M31(2)),x.add(x));
            assert_eq!(x.mul_qm31(q(2)),x.add(x));
        }
        let mixed=QM31{c0:CM31::ONE,c1:CM31::ONE};
        let raw=QM31{c0:CM31::new(M31(u32::MAX),M31::ZERO),c1:CM31::new(M31(u32::MAX),M31::ZERO)};
        let w=WideExact::from_qm31(mixed);
        let native=w.mul_qm31(raw);
        let kit=(km(w.c0(),raw),km(w.c1(),raw));
        std::println!("KSA mixed noncanonical native={:?} kit={:?}",native.to_limbs(),kit);
        assert!(native.c0()!=kit.0 || native.c1()!=kit.1);
        assert_eq!(QM31::from_le_bytes(&[0u8;16]),Some(QM31::ZERO));
        assert!(std::panic::catch_unwind(||QM31::from_le_bytes(&[])).is_err());
        assert_eq!(QM31::from_le_bytes(&[0u8;17]),Some(QM31::ZERO));
        std::println!("KSA QM31 empty native=panic kit=none; 17 zero bytes native=some zero kit=none");
        assert_eq!(WideExact::from_le_bytes(&[]),None);
        assert_eq!(WideExact::ZERO.to_le_bytes(),[0u8;32]);
        assert_eq!(WideExact::ZERO.to_limbs(),[0u32;8]);
        assert_eq!(<WideExact as super::r0::CodeField>::from_m31(M31(P)),WideExact::ZERO);
        assert_eq!(M31(1).add(M31(2)),M31(3));
        assert_eq!(M31(2).sub(M31(1)),M31(1));
        assert_eq!(M31(2).double(),M31(4));
        assert_eq!(M31::reduce_u64(2147483648),M31(1));
        assert_eq!(super::r0::domain::FibreIndex::new(262144),Err(super::r0::Error::IndexOutOfRange));
        assert_eq!(super::r0::domain::FibreIndex::new(2).unwrap().get(),2);
        assert_eq!(super::r0::merkle::C1_TAG,113);assert_eq!(super::r0::merkle::C2_TAG,241);
        std::println!("KSA byte, field, domain and tag fixtures passed");
        // Frozen selected_mask_value, coefficients zero, explicit one, z0=1.
        let mut point=[QM31::ZERO;10];point[0]=QM31::ONE;
        let native=super::state_only_hiding::state_only_selected_mask_value(&[QM31::ZERO;16],&[QM31::ZERO;10],QM31::ONE,&point);
        let kit=QM31::ONE.add(kit_pow(q(275),26));
        std::println!("KSA mask native={:?} kit={:?}",native,kit);assert_ne!(native,kit);
        for t in [QM31{c0:CM31::ZERO,c1:CM31::ONE},QM31{c0:CM31::ONE,c1:CM31::ONE}] {
            let native=super::circle::secure_ood_circle_point_from_parameter(t).unwrap();
            let square=t.mul(t);let inv=kit_pow(QM31::ONE.add(square),u128::from(P).pow(4)-2);
            let kit=(QM31::ONE.sub(square).mul(inv),t.add(t).mul(inv));
            std::println!("KSA circle t={:?} native={:?} kit={:?}",t,native,kit);
            assert!(native.x!=kit.0 || native.y!=kit.1);
        }
    }
}
