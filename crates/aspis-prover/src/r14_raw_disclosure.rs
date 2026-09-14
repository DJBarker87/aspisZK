//! Monotonicity of the existing C1 separator under q22 extension.
//! This binds the algebraic source block, NOT the honest sampler's probability.
#![cfg(feature = "insecure-spend-fixture")]
use aspis_core::field::M31;
use super::CircleEncoder;
use crate::v8_privacy_affine_gate::{verify_fixed_affine_certificate, AffineCertificate};
use aspis_statement::pool_v1::{pool_v1_pair_forest_copy_active_rows_v1,
    pool_v1_pair_forest_relation_free_mask_cells_v1};
#[test]
fn r14_q4_q6_separator_lifts_to_twenty_two_queries(){
    let encoder=CircleEncoder::new_for_domain_log(20);
    let active=pool_v1_pair_forest_copy_active_rows_v1().unwrap();
    let cells=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let rows:Vec<_>=cells.iter().filter(|x|x.column==0 && x.row!=1023).map(|x|usize::from(x.row)).collect();
    let queries=[4usize,6,103685,223415,21813,185513,212496,16679,187089,157035,195744,244899,
        19086,92907,159274,218276,18837,12291,224498,187006,38787,56305];
    let mut mask=Vec::new();let mut target=Vec::new();
    for query in queries{for slot in 0..4{
        let index=4*query+slot;let dep=encoder.encode_c1_basis_value(1023,index).unwrap();
        mask.push(rows.iter().map(|&row|{
            let v=encoder.encode_c1_basis_value(row,index).unwrap();
            if active.contains(&(row as u16)){v}else{v.sub(dep)}
        }).collect());
        target.push(vec![encoder.encode_c1_basis_value(913,index).unwrap()]);
    }}
    let mut lambda=vec![M31::ZERO;88];
    let fixed=[1508290849,1480589898,639192798,666893749,2147483646,0,1,0];
    for i in 0..8{lambda[i]=M31(fixed[i]);}
    verify_fixed_affine_certificate(&mask,&target,&AffineCertificate::Separator{
        rank:0,lambda,target_column:0,nonzero:M31(490597912)
    }).unwrap();
}
