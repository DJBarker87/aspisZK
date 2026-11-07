use super::*;
use crate::NMX_217_reference as R;
pub const INVERSE: bool = option_env!("NMX_217_INVERSE").is_some();
pub fn result_matches(r: &Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>, bytes:&[u8])->bool {
    match (r,R::decode_lane_ref(bytes)) {
        (Err(ProgramError::InvalidAccountData),Err(()))=>true,
        (Ok(a),Ok(b))=>a.bump==b.bump && a.master==b.master && a.lane_id==b.lane_id
            && a.tree.next_leaf_index==b.next_leaf_index
            && a.tree.root.map(|x|x.0)==b.root && a.tree.frontier.map(|row|row.map(|x|x.0))==b.frontier,
        _=>false,
    }
}
// A symbolic small slice exercises the first, length-only source arm.
// This local native check is not generalized to other lengths without a
// separate byte-independent length-arm transport.
#[kani::proof_for_contract(super::decode_lane_from_pool_release)]
#[kani::unwind(2)]
fn NMX_217_wrong_length() {
    let b:[u8;1]=kani::any();
    let n:usize=kani::any(); kani::assume(n<=1);
    let _=super::decode_lane_from_pool_release(&b[..n]);
}
