    for j in 0..a.weights.len() {
        a.weights[j]=a.weights[j].add(a.power.mul_m31(basis[j]));
        crate::trace::value(12,a.next*a.weights.len()+j,E::from_qm31(a.weights[j]));
        crate::trace::value(13,a.next*a.weights.len()+j,E::from_m31(basis[j]));
    }
