#[derive(Clone, Copy)]
struct QM31;
impl QM31 {
    const ZERO: Self = Self;
}

#[inline(always)]
pub(crate) fn array_from_fn_copy<T: Copy, const N: usize>(
    init: T,
    mut f: impl FnMut(usize) -> T,
) -> [T; N] {
    let mut out = [init; N];
    let mut i = 0usize;
    while i < N {
        out[i] = f(i);
        i += 1;
    }
    out
}

fn terminal_selector(claims: &[[QM31; 29]; 3]) -> [QM31; 84] {
    crate::array_from_fn_copy::<_, 84>(QM31::ZERO, |i| claims[i / 28][i % 28])
}

fn selected_claim(claims: &[QM31; 84], row: usize, column: usize) -> QM31 {
    claims[row * 28 + column]
}

struct Openings {
    z: [QM31; 16],
    succ_z: [QM31; 16],
    xor12_z: [QM31; 16],
}
const C1_COLUMNS: usize = 16;

fn composition_gathers(claims: &[QM31; 84]) -> (Openings, [QM31; 10]) {
    let openings = Openings {
        z: crate::array_from_fn_copy::<_, 16>(QM31::ZERO, |column| selected_claim(claims, 0, column)),
        succ_z: crate::array_from_fn_copy::<_, 16>(QM31::ZERO, |column| selected_claim(claims, 1, column)),
        xor12_z: crate::array_from_fn_copy::<_, 16>(QM31::ZERO, |column| selected_claim(claims, 2, column)),
    };
    let mask_only = crate::array_from_fn_copy::<_, 10>(QM31::ZERO, |column| {
        selected_claim(claims, 0, C1_COLUMNS + column)
    });
    (openings, mask_only)
}
