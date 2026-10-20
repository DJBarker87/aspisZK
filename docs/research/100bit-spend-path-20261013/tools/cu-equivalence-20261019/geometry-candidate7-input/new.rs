use crate::{field::M31,verifier::Error,domain};
use alloc::vec::Vec;
pub struct Front{pub flat:Vec<M31>,pub line_z_values:Vec<M31>}
pub fn front(queries:&[u32;22],start:usize,end:usize)->Result<Front,Error>{
        if start>end||end>queries.len(){return Err(Error::Query);}
        let mut line_z_values=Vec::with_capacity(end-start);
        let mut flat=Vec::with_capacity((end-start)*5);
        for &query in &queries[start..end] {
            let (values,line_z)=row(query)?;
            flat.extend_from_slice(&values);
            line_z_values.push(line_z);
        }
        Ok(Front{flat,line_z_values})
}
pub fn row(query:u32)->Result<([M31;5],M31),Error>{
            let u=query as usize;
            let fibre=domain::FibreIndex::new(u).map_err(|_|Error::Query)?;
            let point=crate::fast_domain::fibre_point(fibre);
            let line_x=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4).map_err(|_|Error::Query)?);
            let line_y=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4+3).map_err(|_|Error::Query)?);
            let line_z=line_x.mul(line_x).double().sub(M31::ONE);
            let values=[point.x,point.y,line_x,line_y,line_z];
            if values.iter().any(|x|*x==M31::ZERO){return Err(Error::Query);}
    Ok((values,line_z))
}
pub fn node(folds:usize,index:usize)->M31{
    let mut node=crate::fast_domain::line_node(domain::FibreIndex::new(if folds==1 {index}else{index/4*4}).unwrap());
    if folds==2 {for _ in 0..2 {node=node.mul(node).double().sub(M31::ONE);}}
    node
}
pub fn cached_node(line_z:&[M31],i:usize,start:usize)->M31{
        let z=line_z[i-start];
        z.mul(z).double().sub(M31::ONE)
}
