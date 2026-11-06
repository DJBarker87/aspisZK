use super::*;
use aspis_core::field::{M31,CM31};
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn k(x:[u32;4])->K{K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn e(x:[u32;8])->E{E::new(k([x[0],x[1],x[2],x[3]]),k([x[4],x[5],x[6],x[7]]))}
fn check(){
 let roots:[[u8;32];2]=kani::any();let state:[u8;32]=kani::any();
 let gamma=e(kani::any());let kappa=e(kani::any());let alpha=[e(kani::any()),e(kani::any())];let rho=k(kani::any());let claim=e(kani::any());
 let queries:[u32;22]=kani::any();let semantic_alpha=[k(kani::any()),k(kani::any()),k(kani::any()),k(kani::any()),k(kani::any()),k(kani::any()),k(kani::any()),k(kani::any()),k(kani::any()),k(kani::any())];
 let z=[SecureCirclePoint{x:k(kani::any()),y:k(kani::any())},SecureCirclePoint{x:k(kani::any()),y:k(kani::any())}];
 let original=Box::new(Prepared{variant:Variant::S2,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state});
 let allocated=&*original as *const Prepared;
 let mut result=if cfg!(NJC_bad_alloc){Box::new(Prepared{variant:Variant::S2,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state})}else{original};
 if cfg!(NJC_invert){result.gamma=if gamma==E::ZERO{E::ONE}else{E::ZERO};}
 assert!((&*result as *const Prepared)==allocated);
 assert!(result.variant==Variant::S2);assert_eq!(result.roots,roots);assert_eq!(result.gamma,gamma);assert_eq!(result.kappa,kappa);assert_eq!(result.alpha,alpha);assert_eq!(result.rho,rho);assert_eq!(result.queries,queries);assert_eq!(result.semantic_alpha,semantic_alpha);assert_eq!(result.claim,claim);assert_eq!(result.state,state);
 assert_eq!(result.z[0].x,z[0].x);assert_eq!(result.z[0].y,z[0].y);assert_eq!(result.z[1].x,z[1].x);assert_eq!(result.z[1].y,z[1].y);
}
#[kani::proof]
#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prepared_box(){check();}
#[kani::proof]
#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prepared_box_renamed(){check();}
