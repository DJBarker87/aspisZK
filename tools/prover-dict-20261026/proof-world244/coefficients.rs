#[cfg(not(feature="copy-only"))]
use aspis_r1_cost_probe::transport::Variant;

/// Same call pattern as Variant::coefficients, using an initialized owned array.
/// Copy is the only element operation. No allocation, Drop, or callback is added.
#[cfg(not(feature="copy-only"))]
pub fn owned<T: Copy>(variant: Variant, rows: &[T; 1024]) -> [T; 1024] {
    let mut out = *rows;
    let mut index = 0;
    while index < 1024 {
        out[index] = rows[super::row::row(variant,index)];
        index += 1;
    }
    out
}

/// A pure array-from_fn pattern, with no row-permutation dependency.
pub fn copy_owned<T: Copy>(rows: &[T; 1024]) -> [T; 1024] {
    let mut out = *rows;
    let mut index = 0;
    while index < 1024 {
        out[index] = rows[index];
        index += 1;
    }
    out
}

