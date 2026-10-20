
    let queries=core::array::from_fn(|_|u32::from_le_bytes(r.raw()));
    for (i,q) in queries.iter().enumerate(){if *q>=1<<18||queries[..i].contains(q){return Err(Error::Checkpoint);}}
    let mut semantic_alpha=[K::ZERO;10];for x in &mut semantic_alpha {*x=r.k()?;}
    let z=[SecureCirclePoint{x:r.k()?,y:r.k()?},SecureCirclePoint{x:r.k()?,y:r.k()?}];
    let claim=r.e()?;let rhs=r.e()?;