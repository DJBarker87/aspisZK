// Indexed owned reference for the frozen constructor. No iterator adapters.
fn geometry_owned(queries:[u32;22],start:usize,end:usize)->Result<QueryGeometry,Error> {
    if start>end || end>22 {return Err(Error::Query);}
    let mut line_z=Vec::with_capacity(end-start);
    let mut flat=Vec::with_capacity(5*(end-start));
    let mut index=start;
    while index<end {
        let u=queries[index] as usize;
        let fibre=domain::FibreIndex::new(u).map_err(|_|Error::Query)?;
        let domain::Point{x:cx,y:cy}=fast_domain::fibre_point(fibre);
        let x=fast_domain::line_node(domain::FibreIndex::new(u/4*4).map_err(|_|Error::Query)?);
        let y=fast_domain::line_node(domain::FibreIndex::new(u/4*4+3).map_err(|_|Error::Query)?);
        let z=x.mul(x).double().sub(M31::ONE);
        if cx==M31::ZERO || cy==M31::ZERO || x==M31::ZERO || y==M31::ZERO || z==M31::ZERO {return Err(Error::Query);}
        flat.push(cx);flat.push(cy);flat.push(x);flat.push(y);flat.push(z);
        line_z.push(z);index+=1;
    }
    if flat.len()==0 {return Ok(QueryGeometry{start,inverses:Vec::new(),line_z});}
    let mut prefixes=Vec::with_capacity(flat.len());
    let mut product=M31::ONE;
    let mut index=0;
    while index<flat.len() {prefixes.push(product);product=product.mul(flat[index]);index+=1;}
    let mut suffix_inverse=product.inv();
    let mut flat_inverse=alloc::vec![M31::ZERO;flat.len()];
    let mut index=flat.len();
    while index>0 {index-=1;flat_inverse[index]=suffix_inverse.mul(prefixes[index]);suffix_inverse=suffix_inverse.mul(flat[index]);}
    let mut inverses=Vec::with_capacity(line_z.len());
    let mut index=0;
    while index<line_z.len() {
        inverses.push([flat_inverse[5*index],flat_inverse[5*index+1],flat_inverse[5*index+2],flat_inverse[5*index+3],flat_inverse[5*index+4]]);
        index+=1;
    }
    Ok(QueryGeometry{start,inverses,line_z})
}
