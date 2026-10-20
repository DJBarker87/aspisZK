    let mut node=crate::fast_domain::line_node(domain::FibreIndex::new(if p.variant.folds()==1 {index}else{index/4*4}).unwrap());
    if p.variant.folds()==2 {for _ in 0..2 {node=node.mul(node).double().sub(M31::ONE);}}
