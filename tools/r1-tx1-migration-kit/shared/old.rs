use super::shared::*;
pub fn tx1<H:Digest32>(public:Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
    if k>22 {return Err(Error::Parse);}
    let v=View::parse(proof)?;mark(obs,Phase::Parsed);
    let sem=crate::r1_semantic::verify_observed(public,v.semantic,hash,obs).map_err(|_|Error::Semantic)?;mark(obs,Phase::Semantic);
    let p=Prepared::new(&sem,&v,hash)?;let mut a=Accumulator::new(v.variant)?;let g=powers::<29>(p.gamma);mark(obs,Phase::Prepare);
    let geometry=QueryGeometry::for_range(&p.queries,0,k)?;
    while a.next<k {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry)?;}
    let bytes=checkpoint_result(&p,&a,proof,public_bytes,hash)?;mark(obs,Phase::CheckpointWrite);Ok(bytes)
}
