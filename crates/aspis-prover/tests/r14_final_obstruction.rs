//! Fixed-C1 final-round obstruction, tested against literal mask factors.
//! Arbitrary opening values are permitted in this algebra test; NOT a witness.
#![cfg(feature = "insecure-spend-fixture")]
use aspis_core::{field::{QM31,CM31,M31},state_only_hiding::state_only_selected_mask_value};
fn q(n:u32)->QM31{QM31::from_cm31(CM31::from_m31(M31(n)))}
fn interpolate(values:&[QM31])->Vec<QM31>{
    let n=values.len();let mut out=vec![QM31::ZERO;n];
    for i in 0..n{
        let mut basis=vec![QM31::ONE];
        for j in 0..n{
            if i==j{continue}let mut next=vec![QM31::ZERO;basis.len()+1];
            let scale=q(i as u32).sub(q(j as u32)).inv();
            for k in 0..basis.len(){next[k]=next[k].sub(basis[k].mul(q(j as u32)));next[k+1]=next[k+1].add(basis[k]);}
            basis=next.into_iter().map(|x|x.mul(scale)).collect();
        }
        for k in 0..n{out[k]=out[k].add(values[i].mul(basis[k]));}
    }out
}
fn check_high(poly:&[QM31],a:QM31){
    let alpha=a.mul(q(1625).inv());
    for (j,m,n,power) in [(23usize,2600u32,52650u32,3u64),(24,325,5850,2),(25,26,351,1)]{
        let value=poly[j].sub(q(m).mul(alpha.pow(power)).mul(poly[26]))
            .add(q(n).mul(alpha.pow(power+1)).mul(poly[27]));
        assert_eq!(value,QM31::ZERO,"high invariant c{j}");
    }
}
#[test]
fn r14_g_and_all_mask_only_lanes_leave_three_high_invariants(){
    let ext=QM31{c0:CM31::new(M31(2),M31(3)),c1:CM31::new(M31(5),M31(7))};
    for mode in 0..4{
        let mut z=[QM31::ZERO;10];
        for j in 0..9{z[j]=match mode{0=>QM31::ZERO,1=>QM31::ONE,2=>q(j as u32+19),_=>ext.mul(q(j as u32+1))};}
        let a=(0..9).fold(QM31::ZERO,|s,j|s.add(q(275+150*j as u32).mul(z[j])));
        let values:Vec<_>=(0..28).map(|t|{
            let x=q(t);z[9]=x;
            let mask=core::array::from_fn(|j|ext.mul(q(j as u32+1)).add(x.mul(q(2*j as u32+3))));
            let g=ext.add(x.mul(ext.mul(ext)));
            state_only_selected_mask_value(&[QM31::ZERO;16],&mask,g,&z)
        }).collect();
        check_high(&interpolate(&values),a);
    }
}
