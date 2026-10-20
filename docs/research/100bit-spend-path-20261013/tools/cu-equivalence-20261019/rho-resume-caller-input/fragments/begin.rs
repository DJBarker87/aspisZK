
    if bytes.len()!=checkpoint_size(v)||&bytes[..8]!=b"R1P2CKP2"||bytes[8]!=v.tag()||bytes[9]>22||bytes[10]!=1||bytes[11..16].iter().any(|&b|b!=0) {return Err(Error::Checkpoint);}
    let end=bytes.len()-32;
    if bytes[16..48]!=hash.digest(&[proof])||bytes[48..80]!=hash.digest(&[public])||bytes[end..]!=hash.digest(&[b"UNPROVED:R1:checkpoint",&bytes[..end]]) {return Err(Error::Checkpoint);}
    let mut r=Reader{bytes,at:80};let state=r.raw();let roots=[r.raw(),r.raw()];
    let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];