// Pure descriptor projection, shared with the step-wise Kani gate.
pub fn describe(sid: &[(u32, u32)]) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let pr = |li: u32| if li < 10 { 1 } else { 4 };
    (
        sid.iter().map(|&(li, _)| li).collect(),
        sid.iter().map(|&(li, j)| j / pr(li) + 1).collect(),
        sid.iter().map(|&(li, j)| j % pr(li)).collect(),
    )
}
