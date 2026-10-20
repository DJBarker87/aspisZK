pub fn resume_read_queries(bytes:&[u8],at:usize)->Result<([u32;22],usize),Error> {
    let mut r=Reader{bytes,at};
    let queries=core::array::from_fn(|_|u32::from_le_bytes(r.raw()));
    for (i,q) in queries.iter().enumerate(){if *q>=1<<18||queries[..i].contains(q){return Err(Error::Checkpoint);}}
    Ok((queries,r.at))
}
