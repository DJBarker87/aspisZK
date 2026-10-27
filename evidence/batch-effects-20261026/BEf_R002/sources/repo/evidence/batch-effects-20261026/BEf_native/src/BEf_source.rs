fn opening(proof: &[u8], i: usize) -> &[u8] {
    let at = compact::OFF_OPENINGS + i * OPENING;
    &proof[at..at + OPENING]
}

fn slot(proof: &[u8], s: usize) -> &[u8] {
    &proof[compact::slot_offset(s)..compact::slot_offset(s + 1)]
}

fn batch_keys(queries: &[u32; 22], lo: usize, n: usize, tree: usize) -> [u64; multiproof::MAX_BATCH] {
    let mut keys = [0u64; multiproof::MAX_BATCH];
    for j in 0..n {
        let u = queries[lo + j];
        let index = if tree == 2 { u / 4 } else { u };
        keys[j] = (u64::from(index) << 8) | j as u64;
    }
    keys
}

fn sort_batch_keys(mut keys: [u64; multiproof::MAX_BATCH], n: usize) -> [u64; multiproof::MAX_BATCH] {
    for i in 1..n {
        let mut j = i;
        while j > 0 && batch_key_at(&keys, j - 1) > batch_key_at(&keys, j) {
            keys.swap(j - 1, j);
            j -= 1;
        }
    }
    keys
}

fn batch_leaf<H: Digest32>(hash: H, tree: usize, q: &[u8]) -> [u8; 32] {
    match tree {
        0 => {
            let salt: [u8; 32] = q[608..640].try_into().unwrap();
            private_leaf_hash_with_digest(hash, merkle::C1_TAG, &q[..480], &salt)
        }
        1 => {
            let salt: [u8; 32] = q[640..672].try_into().unwrap();
            private_leaf_hash_with_digest(hash, merkle::C2_TAG, &q[480..608], &salt)
        }
        _ => {
            let salt: [u8; 32] = q[800..832].try_into().unwrap();
            private_leaf_hash_with_digest(hash, 0x72, &q[672..800], &salt)
        }
    }
}

fn same_batch_leaf(values: &[[u8; 32]; multiproof::MAX_BATCH], index: usize, leaf: [u8; 32]) -> bool {
    values[index] == leaf
}

fn same_batch_index(values: &[u32; multiproof::MAX_BATCH], index: usize, expected: u32) -> bool {
    values[index] == expected
}

fn batch_key_at(keys: &[u64; multiproof::MAX_BATCH], index: usize) -> u64 {
    keys[index]
}

fn batch_merkle_values<H: Digest32>(proof: &[u8], queries: [u32; 22], roots: [[u8; 32]; 3], batch: usize, hash: H) -> Result<(), Error> {
    let mut idx = [0u32; multiproof::MAX_BATCH];
    let mut val = [[0u8; 32]; multiproof::MAX_BATCH];
    let [root0, root1, root2] = roots;
    batch_tree(proof, queries, root0, batch, 0, &mut idx, &mut val, hash)?;
    batch_tree(proof, queries, root1, batch, 1, &mut idx, &mut val, hash)?;
    batch_tree(proof, queries, root2, batch, 2, &mut idx, &mut val, hash)?;
    Ok(())
}

fn batch_tree<H: Digest32>(proof: &[u8], queries: [u32; 22], root: [u8; 32], batch: usize, tree: usize, idx: &mut [u32; multiproof::MAX_BATCH], val: &mut [[u8; 32]; multiproof::MAX_BATCH], hash: H) -> Result<(), Error> {
    let (lo, hi) = if batch == 0 { (0, SPLIT) } else { (SPLIT, 22) };
    let n = hi - lo;
    let s = 3 * batch + tree;
    let keys = sort_batch_keys(batch_keys(&queries, lo, n, tree), n);
    let mut d = 0;
    let mut key_position = 0;
    while key_position < n {
        let key = batch_key_at(&keys, key_position);
        key_position += 1;
        let index = (key >> 8) as u32;
        let q = opening(proof, lo + (key & 0xff) as usize);
        let leaf = batch_leaf(hash, tree, q);
        if d > 0 && same_batch_index(idx, d - 1, index) {
            if !same_batch_leaf(val, d - 1, leaf) {
                return Err(Error::Merkle);
            }
            continue;
        }
        idx[d] = index;
        val[d] = leaf;
        d += 1;
    }
    let count = multiproof::node_count(Arity::Two, &idx[..d]).ok_or(Error::Merkle)?;
    let nodes = slot(proof, s);
    // Padding is whole 32-byte words: scan it 8 bytes at a time.
    if count > SLOT_NODES[s] || nodes[32 * count..].chunks_exact(8).any(|w| u64::from_le_bytes(w.try_into().unwrap()) != 0) {
        return Err(Error::Parse);
    }
    if !multiproof::verify_in_place(hash, Arity::Two, &root, idx, val, d, &nodes[..32 * count]) {
        return Err(Error::Merkle);
    }
    Ok(())
}

fn BEf_source_tail<H: Digest32>(proof: &[u8], root: [u8;32], s: usize, idx: &mut [u32; multiproof::MAX_BATCH], val: &mut [[u8;32]; multiproof::MAX_BATCH], d: usize, hash: H) -> Result<(), Error> {
    let count = multiproof::node_count(Arity::Two, &idx[..d]).ok_or(Error::Merkle)?;
    let nodes = slot(proof, s);
    // Padding is whole 32-byte words: scan it 8 bytes at a time.
    if count > SLOT_NODES[s] || nodes[32 * count..].chunks_exact(8).any(|w| u64::from_le_bytes(w.try_into().unwrap()) != 0) {
        return Err(Error::Parse);
    }
    if !multiproof::verify_in_place(hash, Arity::Two, &root, idx, val, d, &nodes[..32 * count]) {
        return Err(Error::Merkle);
    }
    Ok(())
}
