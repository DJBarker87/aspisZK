include!("balance_cut.rs");
fn main() {
    let mut cases = 0;
    let mut changed = 0;
    for seed in 0..64u32 {
        let mut active = [false; 1024];
        for i in 0..1024 { active[i] = (i + seed as usize) % 5 == 0; }
        let d = (seed as usize * 13 + 1) % 1024;
        active[d] = false;
        let table: Vec<QM31> = (0..1024).map(|i| {
            let v = (seed.wrapping_mul(7919) + i * 104729) % aspis_core::field::P;
            QM31 { c0: aspis_core::field::CM31::new(M31(v),M31((v+1)%aspis_core::field::P)),
                   c1: aspis_core::field::CM31::new(M31((v+2)%aspis_core::field::P),M31((v+3)%aspis_core::field::P)) }
        }).collect();
        let mut native = table.clone();
        let before = native[d];
        let a = balance_qm31_copy_inactive(&mut native, d, &active);
        let (b, reference) = balance_qm31_owned(table, d, &active);
        assert_eq!(a,b); assert_eq!(native,reference);
        if native[d] != before { changed += 1; }
        for i in 0..1024 { if i != d { assert_eq!(native[i],reference[i]); } }
        cases += 1;
        let scalar: Vec<M31> = (0..1024).map(|i| M31((seed*7919+i*104729)%aspis_core::field::P)).collect();
        let mut native = scalar.clone();
        let before = native[d];
        let a = balance_m31_copy_inactive(&mut native, d, &active);
        let (b, reference) = balance_m31_owned(scalar, d, &active);
        assert_eq!(a,b); assert_eq!(native,reference);
        if native[d] != before { changed += 1; }
        cases += 1;
    }
    assert_eq!(changed,128);
    println!("FINITE VALIDATION: {cases} same-input native/reference successful results, full output vectors equal; {changed} changed dependent writes. Not a universal proof or honest-fixture association.");
}
