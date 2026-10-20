pub fn query<H:Digest32>(v:&View<'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:H,obs:Observer)->Result<(),Error> {
    let geometry=QueryGeometry::for_range(&p.queries,a.next,a.next+1)?;
    query_with_geometry(v,p,a,g,hash,obs,&geometry)
}