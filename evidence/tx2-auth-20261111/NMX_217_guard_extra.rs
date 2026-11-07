// Source cut of the ACTUAL first guard at frozen r1_pool_adapter.rs:452.
// Only substitution: bytes.len() is the scalar argument n.
#[kani::modifies()]
#[kani::ensures(|r: &bool| (*r == (n != 768)) != INVERSE)]
fn NMX_217_first_guard(n:usize)->bool {
    n != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES
}
#[kani::proof_for_contract(NMX_217_first_guard)]
fn NMX_217_all_lengths(){let n:usize=kani::any();let _=NMX_217_first_guard(n);}
