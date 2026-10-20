pub fn tx2_authenticated<H:Digest32>(public_bytes:&[u8],proof:&[u8],checkpoint:&[u8],hash:H,obs:Observer)->Result<(),Error> {
    let v=View::parse_shape(proof)?;mark(obs,Phase::Parsed);
    let (p,mut a)=resume(checkpoint,proof,public_bytes,v.variant,hash)?;let g=powers::<29>(p.gamma);mark(obs,Phase::CheckpointRead);
    let geometry=QueryGeometry::for_range(&p.queries,a.next,22)?;
    while a.next<22 {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry)?;}
    finish_relation(&v,&p,&a,obs)
}