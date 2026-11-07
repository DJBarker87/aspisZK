use super::*;
// Result<Box<Lane>,ProgramError> contract interface controls only.
#[kani::ensures(|r: &Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>| r.is_err())]
#[kani::modifies()]
fn NMX_shape()->Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>{
    Err(ProgramError::InvalidAccountData)
}
#[kani::proof_for_contract(NMX_shape)]
fn NMX_shape_contract(){let _=NMX_shape();}
#[kani::proof]
fn NMX_shape_real(){
    assert!(matches!(NMX_shape(),Err(ProgramError::InvalidAccountData)),"NMX uninferred caller assertion");
}
#[kani::proof]
#[kani::stub_verified(NMX_shape)]
fn NMX_shape_stub(){
    assert!(matches!(NMX_shape(),Err(ProgramError::InvalidAccountData)),"NMX uninferred caller assertion");
}
#[kani::modifies()]
#[kani::ensures(|r: &Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>| r.is_err())]
fn NMX_shape_write(x:&mut u8)->Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>{
    *x=1; Err(ProgramError::InvalidAccountData)
}
#[kani::proof_for_contract(NMX_shape_write)]
fn NMX_shape_modifies(){let mut x=0;let _=NMX_shape_write(&mut x);}
