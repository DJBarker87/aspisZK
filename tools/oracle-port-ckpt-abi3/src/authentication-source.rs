use aspis_r1_cost_probe::verifier::checkpoint_size;
fn authenticate<H:Digest32>(bytes:&[u8],proof:&[u8],public:&[u8],v:Variant,hash:H)->Result<usize,Error> {
    if bytes.len()!=checkpoint_size(v)||&bytes[..8]!=b"R1P2CKP2"||bytes[8]!=v.tag()||bytes[9]>22||bytes[10]!=1||bytes[11..16].iter().any(|&b|b!=0) {return Err(Error::Checkpoint);}
    let end=bytes.len()-32;
    if bytes[16..48]!=hash.digest(&[proof])||bytes[48..80]!=hash.digest(&[public])||bytes[end..]!=hash.digest(&[b"UNPROVED:R1:checkpoint",&bytes[..end]]) {return Err(Error::Checkpoint);}
    Ok(end)
}
