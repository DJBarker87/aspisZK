    if r.at!=end {return Err(Error::Checkpoint);}
    Ok((Box::new(Prepared{variant:v,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state}),Accumulator{weights,rhs,power,next:bytes[9] as usize}))
}