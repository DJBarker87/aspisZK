// Owned recursive traversals avoid the pinned translator's shared-loan loop join.
fn gather_geometry_owned(queries:[u32;22],index:usize,end:usize,mut flat:Vec<M31>,mut zs:Vec<M31>)->Result<(Vec<M31>,Vec<M31>),Error> {
    if index>=end {return Ok((flat,zs));}
    let u=queries[index] as usize;
    let fibre=domain::FibreIndex::new(u).map_err(|_|Error::Query)?;
    let domain::Point{x:cx,y:cy}=fast_domain::fibre_point(fibre);
    let x=fast_domain::line_node(domain::FibreIndex::new(u/4*4).map_err(|_|Error::Query)?);
    let y=fast_domain::line_node(domain::FibreIndex::new(u/4*4+3).map_err(|_|Error::Query)?);
    let z=x.mul(x).double().sub(M31::ONE);
    if cx==M31::ZERO || cy==M31::ZERO || x==M31::ZERO || y==M31::ZERO || z==M31::ZERO {return Err(Error::Query);}
    flat.push(cx);flat.push(cy);flat.push(x);flat.push(y);flat.push(z);zs.push(z);
    gather_geometry_owned(queries,index+1,end,flat,zs)
}
fn prefixes_owned(flat:Vec<M31>,mut prefixes:Vec<M31>,product:M31,index:usize)->(Vec<M31>,Vec<M31>,M31) {
    if index>=flat.len() {return (flat,prefixes,product);}
    prefixes.push(product);
    let product=product.mul(flat[index]);
    prefixes_owned(flat,prefixes,product,index+1)
}
fn inverse_owned(flat:Vec<M31>,prefixes:Vec<M31>,mut inverse:Vec<M31>,suffix:M31,index:usize)->Vec<M31> {
    if index==0 {return inverse;}
    let i=index-1;
    inverse[i]=suffix.mul(prefixes[i]);
    let suffix=suffix.mul(flat[i]);
    inverse_owned(flat,prefixes,inverse,suffix,i)
}
fn groups_owned(flat_inverse:Vec<M31>,mut groups:Vec<[M31;5]>,index:usize,count:usize)->Vec<[M31;5]> {
    if index>=count {return groups;}
    groups.push([flat_inverse[5*index],flat_inverse[5*index+1],flat_inverse[5*index+2],flat_inverse[5*index+3],flat_inverse[5*index+4]]);
    groups_owned(flat_inverse,groups,index+1,count)
}
fn geometry_owned(queries:[u32;22],start:usize,end:usize)->Result<QueryGeometry,Error> {
    if start>end || end>22 {return Err(Error::Query);}
    let (flat,line_z)=gather_geometry_owned(queries,start,end,Vec::with_capacity(5*(end-start)),Vec::with_capacity(end-start))?;
    if flat.len()==0 {return Ok(QueryGeometry{start,inverses:Vec::new(),line_z});}
    let count=flat.len();
    let (flat,prefixes,product)=prefixes_owned(flat,Vec::with_capacity(count),M31::ONE,0);
    let flat_inverse=alloc::vec![M31::ZERO;count];
    let flat_inverse=inverse_owned(flat,prefixes,flat_inverse,product.inv(),count);
    let n=line_z.len();
    let inverses=groups_owned(flat_inverse,Vec::with_capacity(n),0,n);
    Ok(QueryGeometry{start,inverses,line_z})
}
