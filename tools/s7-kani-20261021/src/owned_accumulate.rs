// Fully owned transitions: no mutable-reference input survives a loop backedge.
fn residue_scalar_owned(raw:u64,limb:u32,basis:u32,flush:bool)->u64 {
    let updated=raw+u64::from(limb)*u64::from(basis);
    if flush {(updated&0x7fff_ffff)+(updated>>31)} else {updated}
}
fn residue_owned(row:[u64;4],power:K,basis:M31,flush:bool)->[u64;4] {
    [residue_scalar_owned(row[0],power.c0.a.0,basis.0,flush),
     residue_scalar_owned(row[1],power.c0.b.0,basis.0,flush),
     residue_scalar_owned(row[2],power.c1.a.0,basis.0,flush),
     residue_scalar_owned(row[3],power.c1.b.0,basis.0,flush)]
}
fn push_owned(mut weights:BatchedWeights,index:usize,power:K,basis:M31)->BatchedWeights {
    let row=weights.raw[index];
    let updated=residue_owned(row,power,basis,weights.terms&3==3);
    weights.raw[index]=updated;
    weights
}
fn basis_block_owned(mut basis:[M31;256],node:M31,n:usize,j:usize)->[M31;256] {
    if j>=n {return basis;}
    let value=basis[j].mul(node);basis[n+j]=value;
    basis_block_owned(basis,node,n,j+1)
}
fn basis_levels_owned(basis:[M31;256],node:M31,width:usize,n:usize)->[M31;256] {
    if n>=width {return basis;}
    let basis=basis_block_owned(basis,node,n,0);
    let node=node.mul(node).double().sub(M31::ONE);
    basis_levels_owned(basis,node,width,n*2)
}
fn basis_owned(node:M31,width:usize)->[M31;256] {
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;
    basis_levels_owned(basis,node,width,1)
}
fn accumulate_rows_owned(mut output_weights:Vec<K>,mut weights:BatchedWeights,basis:[M31;256],power:K,next:usize,width:usize,j:usize)->(Vec<K>,BatchedWeights) {
    if j>=width {return (output_weights,weights);}
    weights=push_owned(weights,j,power,basis[j]);
    #[cfg(feature="prover")] {output_weights[j]=weights.value(j);}
    crate::trace::value(12,next*width+j,E::from_qm31(output_weights[j]));
    crate::trace::value(13,next*width+j,E::from_m31(basis[j]));
    accumulate_rows_owned(output_weights,weights,basis,power,next,width,j+1)
}
pub fn accumulate_owned(rho:K,a:Accumulator,node:M31,value:E,weights:BatchedWeights)->(Accumulator,BatchedWeights) {
    let Accumulator{weights:output_weights,rhs,power,next}=a;
    let width=output_weights.len();let basis=basis_owned(node,width);
    let (output_weights,mut weights)=accumulate_rows_owned(output_weights,weights,basis,power,next,width,0);
    weights.terms+=1;
    let rhs=rhs.add(value.mul_qm31(power));crate::trace::value(11,next,rhs);
    (Accumulator{weights:output_weights,rhs,power:power.mul(rho),next:next+1},weights)
}
fn plain_rows_owned(mut output_weights:Vec<K>,basis:[M31;256],power:K,next:usize,width:usize,j:usize)->Vec<K> {
    if j>=width {return output_weights;}
    output_weights[j]=output_weights[j].add(power.mul_m31(basis[j]));
    crate::trace::value(12,next*width+j,E::from_qm31(output_weights[j]));
    crate::trace::value(13,next*width+j,E::from_m31(basis[j]));
    plain_rows_owned(output_weights,basis,power,next,width,j+1)
}
fn accumulate_plain_owned(rho:K,a:Accumulator,node:M31,value:E)->Accumulator {
    let Accumulator{weights:output_weights,rhs,power,next}=a;
    let width=output_weights.len();let basis=basis_owned(node,width);
    let output_weights=plain_rows_owned(output_weights,basis,power,next,width,0);
    let rhs=rhs.add(value.mul_qm31(power));crate::trace::value(11,next,rhs);
    Accumulator{weights:output_weights,rhs,power:power.mul(rho),next:next+1}
}
pub fn accumulate_optional_owned(rho:K,a:Accumulator,node:M31,value:E,pending:Option<BatchedWeights>)->(Accumulator,Option<BatchedWeights>) {
    match pending {
        Some(weights)=>{let (a,weights)=accumulate_owned(rho,a,node,value,weights);(a,Some(weights))},
        None=>(accumulate_plain_owned(rho,a,node,value),None)
    }
}
