use aspis_r1_cost_probe::{verifier::Error,r1_wire::Error as SError};
use aspis_prover::state_only_hiding::StateOnlyMaskBuildError;
fn semantic_error(e:SError)->Error {
    #[cfg(feature="r1p-check")]
    if e==SError::ActivePole { return Error::Rejected; }
    let _=e;
    Error::Semantic
}
fn mask_error(e:StateOnlyMaskBuildError)->Error {
    #[cfg(feature="r1p-check")]
    if e==StateOnlyMaskBuildError::MaskSampleExhausted { return Error::Rejected; }
    let _=e;
    Error::Semantic
}
fn main(){
 let mut n=0;
 let values=[SError::Allocation,SError::RowOrder{expected:0,actual:255},SError::InvalidRow,SError::Tag{row:255},SError::Length{row:0},SError::NonCanonical{row:255,value:usize::MAX},SError::Boundary{round:usize::MAX},SError::Terminal,SError::EqualCirclePoints,SError::TrailingBytes,SError::Public,SError::ActivePole];
 for e in values { assert_eq!(semantic_error(e),if matches!(e,SError::ActivePole){Error::Rejected}else{Error::Semantic});n+=1; }
 for e in [StateOnlyMaskBuildError::ZeroPrivateEntropy,StateOnlyMaskBuildError::ReusedMaskNonce,StateOnlyMaskBuildError::MaskSampleExhausted,StateOnlyMaskBuildError::TraceShape,StateOnlyMaskBuildError::Layout]{assert_eq!(mask_error(e),if matches!(e,StateOnlyMaskBuildError::MaskSampleExhausted){Error::Rejected}else{Error::Semantic});n+=1;}
 println!("{{\"cases\":{n}}}");
}
