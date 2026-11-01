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
fn source_root_00() { check::<0, 1>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_01() { check::<1, 2>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_02() { check::<2, 3>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_03() { check::<3, 4>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_07() { check::<7, 8>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_13() { check::<13, 14>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_20() { check::<20, 21>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_04() { check::<4, 5>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_05() { check::<5, 6>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_06() { check::<6, 7>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_08() { check::<8, 9>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_09() { check::<9, 10>(); }

#[kani::proof]
#[kani::unwind(33)]
fn source_root_10() { check::<10, 11>(); }
