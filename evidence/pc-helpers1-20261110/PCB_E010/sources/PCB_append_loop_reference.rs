#[derive(Clone,Copy)] pub struct M31(pub u32);
pub type Digest=[M31;8];
#[derive(Clone,Copy)] pub struct RootPageHeaderV1 {pub pool:[u8;32],pub page_number:u64,pub first_sequence:u64,pub filled:u16}
const POOL_V1_ROOT_HISTORY_CAPACITY:usize=256;
const PAGE_ROOTS_OFFSET:usize=64;
const PAGE_FILLED_OFFSET:usize=56;
impl M31 {pub fn to_le_bytes(self)->[u8;4] {self.0.to_le_bytes()}}
pub fn encode_digest_canonical(digest: &Digest) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (index, value) in digest.iter().enumerate() {
        bytes[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}
pub fn append_ref(data: &mut [u8], header: RootPageHeaderV1, roots: &[Digest]) {
    debug_assert!(usize::from(header.filled) + roots.len() <= POOL_V1_ROOT_HISTORY_CAPACITY);
    for (offset, root) in roots.iter().enumerate() {
        let slot = usize::from(header.filled) + offset;
        let start = PAGE_ROOTS_OFFSET + slot * 32;
        data[start..start + 32].copy_from_slice(&encode_digest_canonical(root));
    }
    let filled = header.filled + roots.len() as u16;
    data[PAGE_FILLED_OFFSET..58].copy_from_slice(&filled.to_le_bytes());
}
