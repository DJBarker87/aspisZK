// All opening hash methods and samplers are copied without semantic changes.
// Native trace writes return as owned state, including query rejection.
#[cfg(any(kani,aeneas_ref))]
fn tail_control21<H:Digest32,P:crate::transcript::control21::Policy>(hash:H,state:[u8;32],sem:[K;25],z:[[K;2];2],r:&Records,variant:Variant)
  ->(Result<([K;25],[[K;2];2],E,E,E,E,[u32;22],K),Error>,[u8;32],Vec<(u16,usize,E)>) {
    let mut t=crate::transcript::control21::Transcript::<H,P>::new(hash,state,variant);
    let gamma=t.scalar(27,&r.y1,true);
    let kappa=t.scalar(28,&r.inactive,false);
    let alpha0=t.scalar(29,&r.c0,false);
    let mut payload=r.folded_root.to_vec();payload.extend_from_slice(&r.c1);
    let alpha1=t.scalar(30,&payload,false);
    let queries=match t.queries(31,&r.fin) {Ok(q)=>q,Err(e)=>return (Err(e),t.state,t.trace)};
    let rho=t.scalar_k(32,&[]);
    (Ok((sem,z,gamma,kappa,alpha0,alpha1,queries,rho)),t.state,t.trace)
}
