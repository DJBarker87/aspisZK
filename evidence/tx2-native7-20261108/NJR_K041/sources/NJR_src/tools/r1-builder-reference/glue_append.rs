//! Parametric call-trace proof for append-tree structural recursion.
//! The two callees return arbitrary shared values. Every node argument,
//! base-call pointer, node order and call count is checked. This certifies
//! composition only; the callee refinements are separate obligations.
use super::super::*;
fn words() -> [u32;8] { [kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any()] }
fn path() -> [[u32;8];20] { [words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words(), words()] }
fn bits() -> [u32;24] { [kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any()] }
static mut FRONTIER: [[u32;8];20] = [[0;8];20];
static mut EMPTY: [[u32;8];20] = [[0;8];20];
static mut INDEX: u64 = 0;
static mut RETURNS: [[u32;8];20] = [[0;8];20];
static mut STATE: [u32;8] = [0;8];
static mut NODE_CALLS: usize = 0;
static mut BASE_CALLS: usize = 0;
static mut WPTR: *const RW = core::ptr::null();
static mut PPTR: *const RP = core::ptr::null();
fn checked_base(w: &RW, p: &RP) -> [u32;8] {
    assert_eq!(w as *const RW, unsafe { WPTR });
    assert_eq!(p as *const RP, unsafe { PPTR });
    assert_eq!(unsafe { NODE_CALLS },0);
    unsafe { BASE_CALLS += 1; STATE }
}
fn checked_node(left: [u32;8], right: [u32;8]) -> [u32;8] {
    let n = unsafe { NODE_CALLS }; assert!(n < 20);
    assert_eq!(unsafe { BASE_CALLS },1);
    let cur = unsafe { STATE };
    let bit = ((unsafe { INDEX } >> n) & 1) != 0;
    let sib = if bit { unsafe { FRONTIER[n] } } else { unsafe { EMPTY[n] } };
    for i in 0..8 {
        assert_eq!(left[i], if bit { sib[i] } else { cur[i] });
        assert_eq!(right[i], if bit { cur[i] } else { sib[i] });
    }
    unsafe { STATE = RETURNS[n]; NODE_CALLS = n+1; STATE }
}
fn run_tree_case(n: usize) {
    let w = RW { input_value: kani::any(), output_value: kani::any(), change_value: kani::any(),
        sk: words(), salt: words(), bits: [0;24], sibs: [[0;8];24],
        pair_first: words(), pair_occupied: kani::any(), pair_second: words(), pair_inverse: kani::any(),
        recipient_owner: words(), recipient_salt: words(), change_owner: words(), change_salt: words() };
    let p = RP { transfer: kani::any(), asset: kani::any(), next_pair_index: kani::any(),
        frontier: path(), empty: path() };
    assert!(n <= 20);
    unsafe { FRONTIER=p.frontier; EMPTY=p.empty; INDEX=p.next_pair_index; RETURNS=path(); STATE=words();
        WPTR=&w; PPTR=&p; BASE_CALLS=0; NODE_CALLS=0; }
    let actual = app_cur_r(&w,&p,n);
    assert_eq!(unsafe { BASE_CALLS },1); assert_eq!(unsafe { NODE_CALLS },n);
    let expected = unsafe { STATE };
    for i in 0..8 { assert_eq!(actual[i],expected[i]); }
}

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_00() { run_tree_case(0); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_01() { run_tree_case(1); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_02() { run_tree_case(2); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_03() { run_tree_case(3); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_04() { run_tree_case(4); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_05() { run_tree_case(5); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_06() { run_tree_case(6); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_07() { run_tree_case(7); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_08() { run_tree_case(8); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_09() { run_tree_case(9); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_10() { run_tree_case(10); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_11() { run_tree_case(11); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_12() { run_tree_case(12); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_13() { run_tree_case(13); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_14() { run_tree_case(14); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_15() { run_tree_case(15); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_16() { run_tree_case(16); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_17() { run_tree_case(17); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_18() { run_tree_case(18); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_19() { run_tree_case(19); }

#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::out_pair_r, checked_base)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::node_digest_r, checked_node)]
fn append_fixed_20() { run_tree_case(20); }
