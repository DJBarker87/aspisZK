// Evidence-only access to the unchanged first inner hash helpers.
#[cfg(kani)]
pub(crate) fn BEm_occupied<H: Digest32>(hash: H, values: &[[u8;32];MAX_BATCH], index: usize) -> [u8;32] {
    occupied_binary_parent(hash, values, index)
}
#[cfg(kani)]
pub(crate) fn BEm_sibling<H: Digest32>(hash: H, values: &[[u8;32];MAX_BATCH], index: usize, sibling: &[u8], left: bool) -> [u8;32] {
    sibling_binary_parent(hash, values, index, sibling, left)
}
