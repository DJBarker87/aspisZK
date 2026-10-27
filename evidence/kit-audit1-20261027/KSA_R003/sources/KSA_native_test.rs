
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
        let kit=(w.c0().mul(raw),w.c1().mul(raw));
        std::println!("KSA mixed noncanonical native={:?} kit={:?}",native.to_limbs(),kit);
        assert!(native.c0()!=kit.0 || native.c1()!=kit.1);
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
