    for j in 0..a.weights.len() {
        if let Some(weights)=pending.as_deref_mut() {
            weights.push(j,a.power,basis[j]);
            #[cfg(feature="prover")] {a.weights[j]=weights.value(j);}
        } else {a.weights[j]=a.weights[j].add(a.power.mul_m31(basis[j]));}
        crate::trace::value(12,a.next*a.weights.len()+j,E::from_qm31(a.weights[j]));
        crate::trace::value(13,a.next*a.weights.len()+j,E::from_m31(basis[j]));
    }
    if let Some(weights)=pending {weights.terms+=1;}
