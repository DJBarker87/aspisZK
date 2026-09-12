//! FIRST ATTEMPT / NOT COMPILED. Host-only example for an ISOLATED pinned copy.
//! Uses the actual repository layout producer. No source edit/deploy is needed
//! on an active worktree. This verifies inventory, NOT full-view zero knowledge.
use aspis_statement::pool_v1::{
    pool_v1_pair_forest_copy_active_rows_v1,
    pool_v1_pair_forest_relation_free_mask_cells_v1,
};

fn fingerprint(cells: &[(u16, u8)]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for &(r, c) in cells {
        for b in r.to_le_bytes().into_iter().chain([c]) {
            h = (h ^ u64::from(b)).wrapping_mul(0x100000001b3);
        }
    }
    h
}

fn main() {
    let active = pool_v1_pair_forest_copy_active_rows_v1().expect("actual source layout");
    let old: Vec<(u16,u8)> = pool_v1_pair_forest_relation_free_mask_cells_v1()
        .expect("actual source inventory").iter().map(|c| (c.row,c.column)).collect();
    let new: Vec<_> = old.iter().copied().filter(|&c| c != (1014,3)).collect();
    assert_eq!(active.len(),214);
    assert!(active.contains(&1014));
    assert!(!active.contains(&1023));
    assert_eq!(old.len(),3803);
    assert_eq!(new.len(),3802);
    assert_eq!(fingerprint(&old),0xf9daf3d54f4285d1);
    assert_eq!(fingerprint(&new),0x6b661245a56c7189);
    let mut independent = [0usize;16];
    for col in 0..16u8 {
        let dependent = new.iter().filter(|&&(r,c)| c == col && !active.contains(&r))
            .map(|&(r,_)| r).max().expect("inactive free row");
        assert_eq!(dependent,1023);
        independent[col as usize] = new.iter().filter(|&&(r,c)| c == col && r != dependent).count();
    }
    assert_eq!(independent.iter().sum::<usize>(),3786);
    println!("{{\"status\":\"ACTUAL_LAYOUT_INVENTORY_ONLY\",\"independent_semantic_by_column\":{:?},\"global_privacy_proved\":false}}",independent);
}
