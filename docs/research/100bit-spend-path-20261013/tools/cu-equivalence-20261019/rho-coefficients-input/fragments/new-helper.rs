pub fn coefficients(rows:&mut alloc::vec::Vec<aspis_core::field::QM31>,power:aspis_core::field::QM31,next:usize,basis:&[M31;256],mut pending:Option<&mut BatchedWeights>) {
    for j in 0..rows.len() {
        if let Some(weights)=pending.as_deref_mut() {
            weights.push(j,power,basis[j]);
            #[cfg(feature="prover")] {rows[j]=weights.value(j);}
        } else {rows[j]=rows[j].add(power.mul_m31(basis[j]));}
        crate::trace::value(12,next*rows.len()+j,E::from_qm31(rows[j]));
        crate::trace::value(13,next*rows.len()+j,E::from_m31(basis[j]));
    }
    if let Some(weights)=pending {weights.terms+=1;}
}
