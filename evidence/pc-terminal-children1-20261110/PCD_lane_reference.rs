pub struct Tree { pub next_leaf_index: u64, pub root: [u32; 8], pub frontier: [[u32; 8]; 20] }
pub struct Lane { pub master: [u8;32], pub bump: u8, pub lane_id: u8, pub tree: Tree }
pub struct After { pub next_pair_index: u64, pub next_root: [u32;8], pub next_frontier: [[u32;8];20] }
pub fn checked_next(old: u64, next: u64) -> bool { match old.checked_add(1) { Some(n) => n == next, None => false } }
pub fn frontier_step(next: u64, level: u32, node: [u32;8], empty: [u32;8]) -> bool {
    if level >= 20 { return false; }
    if (next >> level) & 1 != 0 { return true; }
    node == empty
}
pub fn finish_lane(old: Lane, after: After) -> Lane {
    Lane { master: old.master, bump: old.bump, lane_id: old.lane_id,
      tree: Tree { next_leaf_index: after.next_pair_index, root: after.next_root, frontier: after.next_frontier } }
}
