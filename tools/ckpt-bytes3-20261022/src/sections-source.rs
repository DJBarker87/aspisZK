fn read_checkpoint_weights(bytes:&[u8],mut at:usize,mut weights:Vec<K>)->Result<(Vec<K>,usize),Error> {
    for out in &mut weights {
        let mut reader=Reader{bytes,at};
        let value=reader.k()?;
        at=reader.at;
        *out=value;
    }
    Ok((weights,at))
}

fn read_checkpoint_semantic_alpha(bytes:&[u8],at:usize)->Result<([K;10],usize),Error> {
    let mut r=Reader{bytes,at};
    let values=[
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
    ];
    Ok((values,r.at))
}
