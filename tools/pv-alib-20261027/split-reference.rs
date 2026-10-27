// Safe owned byte reference, with a separate range-copy loop for source proofs.
pub fn copy_range(data: &[u8], start: usize, count: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut j = 0;
    while j < count {
        out.push(data[start + j]);
        j += 1;
    }
    out
}
pub fn split_reference(data: &[u8], size: usize) -> (Vec<Vec<u8>>, Vec<u8>) {
    let count = data.len() / size;
    let mut blocks = Vec::new();
    let mut i = 0;
    while i < count {
        let block = copy_range(data, i * size, size);
        blocks.push(block);
        i += 1;
    }
    let consumed = count * size;
    let tail = copy_range(data, consumed, data.len() - consumed);
    (blocks, tail)
}
