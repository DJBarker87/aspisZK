mod field;use field::{M31,QM31};const STATE_ONLY_POSEIDON_TRACE_ROWS:usize=1024;const MAX_BATCH:usize=16;const LEAF_BITS:u32=18;
#[derive(Debug)]pub enum StateOnlyMaskBuildError {
    ZeroPrivateEntropy,
    ReusedMaskNonce,
    MaskSampleExhausted,
    TraceShape,
    Layout,
}
fn check_indices(indices:&[u32])->Option<()> {
    if indices.is_empty() || indices.len()>MAX_BATCH {return None;}
    let mut i=0;
    while i<indices.len() {
        if indices[i]>=1<<LEAF_BITS || (i>0 && indices[i-1]>=indices[i]) {return None;}
        i+=1;
    }
    Some(())
}
fn count_parent(level:&[u32;MAX_BATCH],i:usize,n:usize)->(u32,usize) {
    let parent=level[i]>>1;
    let take=if i+1<n && level[i+1]>>1==parent {2} else {1};
    (parent,take)
}
fn count_level(mut level:[u32;MAX_BATCH],n:usize)->([u32;MAX_BATCH],usize,usize) {
    let mut i=0;let mut w=0;let mut missing=0;
    while i<n {
        let (parent,take)=count_parent(&level,i,n);
        level[w]=parent;w+=1;i+=take;missing+=2-take;
    }
    (level,w,missing)
}
fn count_levels(level:[u32;MAX_BATCH],n:usize,depth:u32,count:usize,bits:u32)->usize {
    if depth==bits {return count;}
    let (level,n,missing)=count_level(level,n);
    count_levels(level,n,depth+1,count+missing,bits)
}
fn node_count(indices:&[u32])->Option<usize> {
    check_indices(indices)?;
    let mut level=[0u32;MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    Some(count_levels(level,indices.len(),0,0,LEAF_BITS))
}
fn boolean_point(row:usize)->[QM31;10] {
    let mut point=[QM31::ZERO;10];let mut i=0;
    while i<10 {point[i]=if (row>>(9-i))&1==0 {QM31::ZERO} else {QM31::ONE};i+=1;}
    point
}
fn interpolation_shift(basis:&[M31;28],k:usize)->M31 {
    if k==0 {M31::ZERO} else {basis[k-1]}
}
fn interpolation_basis_cell(mut basis:[M31;28],k:usize,j:usize)->[M31;28] {
    let shifted=interpolation_shift(&basis,k);
    let next=shifted.sub(basis[k].mul(M31(j as u32)));
    basis[k]=next;basis
}
fn interpolation_extend(mut basis:[M31;28],degree:usize,j:usize)->[M31;28] {
    let mut k=degree+2;
    while k>0 {k-=1;basis=interpolation_basis_cell(basis,k,j);}
    basis
}
fn interpolation_basis_steps(basis:[M31;28],denominator:M31,degree:usize,i:usize,j:usize)->([M31;28],M31) {
    if j==28 {return (basis,denominator);}
    if i==j {return interpolation_basis_steps(basis,denominator,degree,i,j+1);}
    let basis=interpolation_extend(basis,degree,j);
    let denominator=denominator.mul(M31(i as u32).sub(M31(j as u32)));
    interpolation_basis_steps(basis,denominator,degree+1,i,j+1)
}
fn interpolation_basis(i:usize)->([M31;28],M31) {
    let mut basis=[M31::ZERO;28];basis[0]=M31::ONE;
    interpolation_basis_steps(basis,M31::ONE,0,i,0)
}
fn interpolation_accumulate(mut out:[QM31;28],basis:&[M31;28],scale:QM31)->[QM31;28] {
    let mut k=0;
    while k<28 {
        let value=out[k];let delta=scale.mul_m31(basis[k]);
        let next=value.add(delta);out[k]=next;k+=1;
    }
    out
}
fn inactive_m31_step(sum:M31,table:&[M31],dependent:usize,active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS],row:usize)->M31 {
    if !active[row] && row!=dependent {sum.add(table[row])} else {sum}
}
fn inactive_qm31_step(sum:QM31,table:&[QM31],dependent:usize,active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS],row:usize)->QM31 {
    if !active[row] && row!=dependent {sum.add(table[row])} else {sum}
}
fn sum_m31_copy_inactive(table:&[M31],dependent:usize,active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS])->M31 {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;
    let mut sum=M31::ZERO;
    let mut row=0;
    while row<rows {
        sum=inactive_m31_step(sum,table,dependent,active,row);
        row+=1;
    }
    sum
}
fn sum_qm31_copy_inactive(table:&[QM31],dependent:usize,active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS])->QM31 {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;
    let mut sum=QM31::ZERO;
    let mut row=0;
    while row<rows {
        sum=inactive_qm31_step(sum,table,dependent,active,row);
        row+=1;
    }
    sum
}
fn balance_m31_copy_inactive(
    table: &mut [M31],
    dependent: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;

    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let sum=sum_m31_copy_inactive(table,dependent,active);
    let value=M31::ZERO.sub(sum);
    table[dependent]=value;
    Ok(())
}
fn balance_qm31_copy_inactive(
    table: &mut [QM31],
    dependent: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;

    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let sum=sum_qm31_copy_inactive(table,dependent,active);
    let value=QM31::ZERO.sub(sum);
    table[dependent]=value;
    Ok(())
}
fn assignment_fill(round:usize,remaining:usize,assignment:usize,mut at:[QM31;10])->[QM31;10]{let mut offset=0;
                    while offset<remaining {
                        at[round+1+offset]=if (assignment>>(remaining-1-offset))&1==0 {QM31::ZERO}else{QM31::ONE};
                        offset+=1;
                    }
                    at}
fn main(){println!("nodes {:?}",node_count(&[1,2,3]));println!("boolean {:?}",boolean_point(37).map(|q|q.c0.a.0));println!("accumulate {:?}",interpolation_accumulate([QM31::ONE;28],&[M31(2);28],QM31::ONE.mul_m31(M31(3))).map(|q|q.c0.a.0));println!("basis_cell {:?}",interpolation_basis_cell([M31(2);28],1,3).map(|q|q.0));println!("extend {:?}",interpolation_extend([M31(2);28],1,3).map(|q|q.0));let(a,d)=interpolation_basis(1);println!("basis {:?} {}",a.map(|q|q.0),d.0);println!("assignment {:?}",assignment_fill(1,3,5,[QM31::ZERO;10]).map(|q|q.c0.a.0));let mut a=[M31::ONE;1024];balance_m31_copy_inactive(&mut a,3,&[false;1024]).unwrap();println!("balance_m31 {}",a[3].0);let mut a=[QM31::ONE;1024];balance_qm31_copy_inactive(&mut a,3,&[false;1024]).unwrap();println!("balance_qm31 {}",a[3].c0.a.0);}
