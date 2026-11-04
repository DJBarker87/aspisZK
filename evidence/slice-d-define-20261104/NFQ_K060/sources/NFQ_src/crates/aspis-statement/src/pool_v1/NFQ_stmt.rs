use super::*;
fn any_variant()->CompiledVariant{if kani::any(){CompiledVariant::PrivateTransfer}else{CompiledVariant::Withdrawal}}
pub(super) fn variant_ref(v:CompiledVariant)->u32{match v{CompiledVariant::PrivateTransfer=>1,CompiledVariant::Withdrawal=>0}}
pub(super) fn copy_ref(v:CompiledVariant)->PoolV1PairForestCompiledVariantV1{match v{CompiledVariant::PrivateTransfer=>PoolV1PairForestCompiledVariantV1::PrivateTransfer,CompiledVariant::Withdrawal=>PoolV1PairForestCompiledVariantV1::Withdrawal}}
#[kani::proof_for_contract(variant_expected_output)]
fn variant_contract(){let _=variant_expected_output(any_variant());}
#[kani::proof_for_contract(copy_variant)]
fn copy_contract(){let _=copy_variant(any_variant());}
impl kani::Arbitrary for PoolV1PairForestCompiledVariantV1{fn any()->Self{if kani::any(){Self::PrivateTransfer}else{Self::Withdrawal}}}
#[kani::modifies()] #[kani::ensures(|_r| true)]
fn weak_enum()->PoolV1PairForestCompiledVariantV1{PoolV1PairForestCompiledVariantV1::PrivateTransfer}
#[kani::proof_for_contract(weak_enum)]
fn enum_real(){assert!(matches!(weak_enum(),PoolV1PairForestCompiledVariantV1::PrivateTransfer));}
#[kani::proof] #[kani::stub_verified(weak_enum)]
fn enum_unimplied(){assert!(matches!(weak_enum(),PoolV1PairForestCompiledVariantV1::PrivateTransfer));}
#[kani::modifies(&mut x[0])] #[kani::ensures(|_r| true)]
fn bad_enum_frame(x:&mut[u8;2])->PoolV1PairForestCompiledVariantV1{x[1]=x[1].wrapping_add(1);PoolV1PairForestCompiledVariantV1::PrivateTransfer}
#[kani::proof_for_contract(bad_enum_frame)]
fn enum_frame(){let mut x:[u8;2]=kani::any();let _=bad_enum_frame(&mut x);}
