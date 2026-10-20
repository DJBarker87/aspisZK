if p.variant.folds()==2 {
 let z=geometry.line_z[i-geometry.start];z.mul(z).double().sub(M31::ONE)
 } else { let index=u;
    let mut node=crate::source_line_node(if p.variant.folds()==1 {index}else{index/4*4});
    if p.variant.folds()==2 {for _ in 0..2 {node=node.mul(node).double().sub(M31::ONE);}}
node }