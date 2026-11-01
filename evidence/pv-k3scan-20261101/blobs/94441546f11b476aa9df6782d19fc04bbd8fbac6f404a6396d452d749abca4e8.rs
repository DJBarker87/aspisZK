// Intended solely as a #[cfg(kani)] child of pool_v1::pair_trace.
// No stubs: each leaf calls the frozen source pool_v1_tree_parent body.
mod constants {
    include!("pair_forest_semantic_terminal_constants.rs");
}
use constants::POOL_V1_PAIR_EMPTY_ROOTS_V1 as ROOTS;
use crate::pool_v1::pool_v1_tree_parent;
use super::{Digest, M31};

fn check<const START: usize, const END: usize>() {
    for level in START..END {
        let input: Digest = if level == 0 {
            [M31::ZERO; 8]
        } else {
            ROOTS[level - 1].map(M31)
        };
        let actual = pool_v1_tree_parent(&input, &input);
        for lane in 0..8 {
            assert_eq!(actual[lane].0, ROOTS[level][lane]);
        }
    }
}

#[kani::proof]
#[kani::unwind(33)]
fn source_roots_00_02() { check::<0, 3>(); }
#[kani::proof]
#[kani::unwind(33)]
fn source_roots_03_05() { check::<3, 6>(); }
#[kani::proof]
#[kani::unwind(33)]
fn source_roots_06_08() { check::<6, 9>(); }
#[kani::proof]
#[kani::unwind(33)]
fn source_roots_09_11() { check::<9, 12>(); }
#[kani::proof]
#[kani::unwind(33)]
fn source_roots_12_14() { check::<12, 15>(); }
#[kani::proof]
#[kani::unwind(33)]
fn source_roots_15_17() { check::<15, 18>(); }
#[kani::proof]
#[kani::unwind(33)]
fn source_roots_18_19() { check::<18, 20>(); }
#[kani::proof]
#[kani::unwind(33)]
fn source_roots_20() { check::<20, 21>(); }
