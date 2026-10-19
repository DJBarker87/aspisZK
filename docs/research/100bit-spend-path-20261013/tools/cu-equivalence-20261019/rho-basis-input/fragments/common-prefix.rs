    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let mut n=1;
    while n<a.weights.len() {for j in 0..n {basis[n+j]=basis[j].mul(node);} node=node.mul(node).double().sub(M31::ONE);n*=2;}
