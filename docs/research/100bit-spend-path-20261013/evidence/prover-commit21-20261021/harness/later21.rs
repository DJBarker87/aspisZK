// Source walk suffix after the accepted finite semantic-row cone.
#[cfg(any(kani,aeneas_ref))]
fn later21<H:Digest32>(hash:H,st:SemanticTranscript<H>,sem:[K;25],r:&Records,variant:Variant)->Result<Drawn,Error> {
    let (z0,st)=wire::circle21::point(st,25,r.semantic[25].clone());
    let z0=z0.map_err(|_|Error::Semantic)?;
    let (z1,st)=wire::circle21::point(st,26,r.semantic[26].clone());
    let z1=z1.map_err(|_|Error::Semantic)?;
    let mut t=Transcript::new(hash,st.state(),variant);
    let gamma=t.scalar(27,&r.y1,true);
    let kappa=t.scalar(28,&r.inactive,false);
    let alpha0=t.scalar(29,&r.c0,false);
    let mut payload=r.folded_root.to_vec();payload.extend_from_slice(&r.c1);
    let alpha1=t.scalar(30,&payload,false);
    let queries=t.queries(31,&r.fin)?;
    let rho=t.scalar_k(32,&[]);
    Ok(Drawn{sem,z:[z0,z1],gamma,kappa,alpha0,alpha1,queries,rho})
}
