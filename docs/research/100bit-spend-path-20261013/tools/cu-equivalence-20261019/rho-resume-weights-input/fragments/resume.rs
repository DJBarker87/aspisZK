#[inline(never)]
pub fn resume<H:Digest32>(bytes:&[u8],proof:&[u8],public:&[u8],v:Variant,hash:H)->Result<(Box<Prepared>,Accumulator),Error> {
    if bytes.len()!=checkpoint_size(v)||&bytes[..8]!=b"R1P2CKP2"||bytes[8]!=v.tag()||bytes[9]>22||bytes[10]!=1||bytes[11..16].iter().any(|&b|b!=0) {return Err(Error::Checkpoint);}
    let end=bytes.len()-32;
    if bytes[16..48]!=hash.digest(&[proof])||bytes[48..80]!=hash.digest(&[public])||bytes[end..]!=hash.digest(&[b"UNPROVED:R1:checkpoint",&bytes[..end]]) {return Err(Error::Checkpoint);}
    let mut r=Reader{bytes,at:80};let state=r.raw();let roots=[r.raw(),r.raw()];
    let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];let rho=r.k()?;
    let queries=core::array::from_fn(|_|u32::from_le_bytes(r.raw()));
    for (i,q) in queries.iter().enumerate(){if *q>=1<<18||queries[..i].contains(q){return Err(Error::Checkpoint);}}
    let mut semantic_alpha=[K::ZERO;10];for x in &mut semantic_alpha {*x=r.k()?;}
    let z=[SecureCirclePoint{x:r.k()?,y:r.k()?},SecureCirclePoint{x:r.k()?,y:r.k()?}];
    let claim=r.e()?;let rhs=r.e()?;let power=r.k()?;
    let mut weights=aspis_core::r0::heap::filled(v.final_len(),K::ZERO).map_err(|_|Error::Allocation)?;
    for x in &mut weights {*x=r.k()?;}
    if r.at!=end {return Err(Error::Checkpoint);}
    Ok((Box::new(Prepared{variant:v,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state}),Accumulator{weights,rhs,power,next:bytes[9] as usize}))
}