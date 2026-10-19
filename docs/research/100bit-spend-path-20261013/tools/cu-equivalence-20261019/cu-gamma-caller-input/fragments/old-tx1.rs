#[inline(never)]
pub fn tx1<H:Digest32>(public:Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
    if k>22 {return Err(Error::Parse);}
    let v=View::parse(proof)?;mark(obs,Phase::Parsed);
    let (_semantic_claims,p)=tx1_prepare(public,&v,hash,obs)?;let mut a=Accumulator::new(v.variant)?;let g=powers::<29>(p.gamma);mark(obs,Phase::Prepare);
    tx1_finish(v,p,a,g,public_bytes,proof,k,hash,obs)
}