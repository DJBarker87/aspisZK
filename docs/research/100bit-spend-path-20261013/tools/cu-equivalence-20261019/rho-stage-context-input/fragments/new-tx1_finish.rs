fn tx1_finish<H:Digest32>(v:View<'_>,p:Box<Prepared>,mut a:Accumulator,g:[E;29],public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
    let geometry=QueryGeometry::for_range(&p.queries,0,k)?;
    let mut pending=BatchedWeights::new(&a.weights)?;
    while a.next<k {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry,Some(&mut pending))?;}
    pending.finish(&mut a.weights);
    let bytes=checkpoint(&p,&a,proof,public_bytes,hash);mark(obs,Phase::CheckpointWrite);Ok(bytes)
}