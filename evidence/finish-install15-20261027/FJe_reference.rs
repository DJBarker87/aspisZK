// Owned safe references. Compiled only in the isolated cfg(kani) evidence crate.
#[cfg(kani)]
#[allow(non_snake_case)]
mod FJe_reference {
    use super::*;

    fn local_raw(input: [QM31; 4]) -> [u64;4] {
        let x = input.map(extension_limbs);
        let t: [[u64; 4]; 4] = core::array::from_fn(|r| core::array::from_fn(|l| {
            let [a,b,c,d] = [x[0][l],x[1][l],x[2][l],x[3][l]].map(u64::from);
            match r { 0 => 2*a+3*b+c+d, 1 => a+2*b+3*c+d,
                2 => a+b+2*c+3*d, _ => 3*a+b+c+2*d }
        }));
        let b = 7*u64::from(P);
        [
            t[0][0]+5*b-t[1][1]+2*t[2][2]-t[2][3]-t[3][2]-2*t[3][3],
            t[0][1]+t[1][0]+t[2][2]+2*t[2][3]+2*t[3][2]+b-t[3][3],
            t[0][2]+2*b-t[1][3]+t[2][0]-t[3][1],
            t[0][3]+t[1][2]+t[2][1]+t[3][0],
        ]
    }

    fn local(input: [QM31;4]) -> QM31 { extension_from_raw_limbs(local_raw(input)) }

    fn external(s: [QM31; 16]) -> [QM31; 4] {
        let p: [QM31; 4] = core::array::from_fn(|g|
            local([s[4*g],s[4*g+1],s[4*g+2],s[4*g+3]]));
        let sum = QM31::ZERO.add(p[0]).add(p[1]).add(p[2]).add(p[3]);
        core::array::from_fn(|g| p[g].add(sum))
    }

    fn m31_packed(s: [QM31; 16], c: [u32; 16]) -> [QM31; 4] {
        let nonlinear = core::array::from_fn(|j| {
            let mut x = s[j]; x.c0.a = x.c0.a.add(M31(c[j])); pow5(x)
        });
        external(nonlinear)
    }

    fn leading(o: &StateOnlyPoseidonOpenings) -> [QM31; 4] {
        let mut s = core::array::from_fn(|j|
            if j < RATE { o.z[j].add(o.xor12_z[j]) } else { o.z[j] });
        external_linear_lazy(&mut s);
        m31_packed(full_round_m31_constants(s, EXTERNAL_INITIAL[0]), EXTERNAL_INITIAL[1])
    }

    fn full(s: [QM31;16], local: &[QM31;16]) -> [QM31;4] {
        let w = [local[1],local[9],local[10]];
        let even = interpolate_three_constant_columns(w,EXTERNAL_INITIAL[2],EXTERNAL_FINAL[0],EXTERNAL_FINAL[2]);
        let odd = interpolate_three_constant_columns(w,EXTERNAL_INITIAL[3],EXTERNAL_FINAL[1],EXTERNAL_FINAL[3]);
        let first = full_round(s,even);
        external(core::array::from_fn(|j| pow5(first[j].add(odd[j]))))
    }

    fn any_q() -> QM31 {
        let x: [u32;4] = kani::any();
        kani::assume(x.iter().all(|v| *v < P));
        QM31 { c0: CM31::new(M31(x[0]),M31(x[1])), c1: CM31::new(M31(x[2]),M31(x[3])) }
    }
    fn any_state() -> [QM31;16] { core::array::from_fn(|_| any_q()) }

    #[kani::proof]
    #[kani::unwind(6)]
    fn local_raw_value() {
        let input: [QM31;4] = core::array::from_fn(|_| any_q());
        assert_eq!(external_local_packed_raw(input),local_raw(input));
        kani::cover!(true, "canonical local inputs inhabited");
    }

    #[kani::proof]
    #[kani::unwind(18)]
    fn external_value() {
        let s = any_state();
        assert_eq!(external_linear_packed(s),external(s));
        kani::cover!(true, "canonical external inputs inhabited");
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn leading_value() {
        let o = StateOnlyPoseidonOpenings {z:any_state(),succ_z:any_state(),xor12_z:any_state()};
        assert_eq!(leading_pair_packed(&o),leading(&o));
        kani::cover!(true, "canonical leading inputs inhabited");
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn full_value() {
        let s = any_state(); let l = any_state();
        assert_eq!(interpolated_full_pair_packed(s,&l),full(s,&l));
        kani::cover!(true, "canonical full inputs inhabited");
    }
}
