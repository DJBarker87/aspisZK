// Drop-free safe reference: caller owns both output buffers.
pub fn copy_range(data: &[u8], start: usize, end: usize, out: &mut Vec<u8>) {
    let mut i = start;
    while i < end {
        out.push(data[i]);
        i += 1;
    }
}
pub fn split_flat_reference(data: &[u8], size: usize,
    blocks: &mut Vec<u8>, tail: &mut Vec<u8>) {
    let count = data.len() / size;
    let consumed = count * size;
    copy_range(data, 0, consumed, blocks);
    copy_range(data, consumed, data.len(), tail);
}
