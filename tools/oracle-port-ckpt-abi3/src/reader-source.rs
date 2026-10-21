struct Reader<'a>{bytes:&'a[u8],at:usize}
impl<'a> Reader<'a>{
    fn raw<const N:usize>(&mut self)->[u8;N] {let b=self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N;b}
    fn e(&mut self)->Result<E,Error>{E::from_le_bytes(&self.raw::<32>()).ok_or(Error::Checkpoint)}
    #[inline(always)]
    fn k(&mut self)->Result<K,Error>{K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)}
}


#[inline(always)]
fn validate_checkpoint_queries(queries:&[u32;22])->Result<(),Error> {
    let mut i=0;
    while i<queries.len() {
        let q=queries[i];
        if q>=1<<18||queries[..i].contains(&q){return Err(Error::Checkpoint);}
        i+=1;
    }
    Ok(())
}

#[inline(always)]
fn read_checkpoint_weights(bytes:&[u8],mut at:usize,mut weights:Vec<K>)->Result<(Vec<K>,usize),Error> {
    for out in &mut weights {
        let mut reader=Reader{bytes,at};
        let value=reader.k()?;
        at=reader.at;
        *out=value;
    }
    Ok((weights,at))
}


#[inline(always)]
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

