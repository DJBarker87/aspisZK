//! OPTIONAL SECOND PROFILE CHANGE. Host generator / test draft, NOT a deployed map.
//! Keep the exact first 89 R16 pad positions, changing only their union with 0..89.
//! Run the source inventory and complete H1/C1/G gates before use. Uncompiled here.

pub const N: usize = 1024;
pub const PADS: usize = 89;

/// Supply the first 89 rows from the ACTUAL immutable R16 constructor.
/// This code does not infer legality or accept a prover-supplied permutation.
pub fn minimal_order(pads: &[usize; PADS]) -> Option<[usize; N]> {
    let mut used = [false; N];
    for &r in pads {
        if r >= 1023 || used[r] { return None; }
        used[r] = true;
    }
    let mut order = core::array::from_fn(|i| i);
    order[..PADS].copy_from_slice(pads);
    let mut missing = 0;
    for &hole in pads {
        if hole >= PADS {
            while missing < PADS && used[missing] { missing += 1; }
            if missing == PADS { return None; }
            order[hole] = missing;
            missing += 1;
        }
    }
    let mut seen = [false; N];
    for &r in &order { if seen[r] { return None; } seen[r] = true; }
    Some(order)
}

/// Host-only inventory: freeze these indices and complete cycle schedules into
/// verifier constants after comparing against the selected source constructor.
pub fn changed_indices(order: &[usize; N], output: &mut [usize; N]) -> usize {
    let mut n = 0;
    for j in 0..N { if order[j] != j { output[n] = j; n += 1; } }
    n
}
// Forward/inverse/dual formulas are exactly R16's, with the new order and SAME
// inactive inventory and pivot 1023. Do not transplant the rejected pivot-13 map.
