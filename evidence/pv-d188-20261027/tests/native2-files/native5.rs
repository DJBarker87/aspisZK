mod field;mod scalar;use field::{QM31,CM31,M31};use scalar::CodeField;
pub fn basis_cell<E:CodeField>(mut out:[E;512],width:usize,j:usize,factor:E)->[E;512] {
    out[width+j]=out[j].mul(factor);out
}

fn cell(mut out:[QM31;27],index:usize,value:QM31)->[QM31;27] {out[index]=value;out}

fn main(){let out=basis_cell([M31(2);512],1,0,M31(3));println!("basis {}",out[1].0);let out=cell([QM31::ZERO;27],5,QM31::ONE);let q=out[5];println!("cell {:?}",[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]);}
