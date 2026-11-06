// Exact frozen batch_tree terminal, exposed on arbitrary loop post-state.
fn terminal_fragment<H:Digest32>(proof:&[u8],root:[u8;32],s:usize,idx:&mut[u32;16],val:&mut[[u8;32];16],d:usize,hash:H)->Result<(),Error>{
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

fn leaf_fragment<H:Digest32>(proof:&[u8],tree:usize,hash:H,lo:usize,n:usize,keys:[u64;16],idx:&mut[u32;16],val:&mut[[u8;32];16],mut d:usize,mut key_position:usize)->Result<(usize,usize),Error>{
 for _ in 0..1 { if key_position<n {
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
 }}
 Ok((d,key_position))
}

fn prefix_fragment<H:Digest32>(proof:&[u8],tree:usize,hash:H,lo:usize,keys:[u64;16],mut key_position:usize)->(u32,[u8;32],usize){
        let key = batch_key_at(&keys, key_position);
        key_position += 1;
        let index = (key >> 8) as u32;
        let q = opening(proof, lo + (key & 0xff) as usize);
        let leaf = batch_leaf(hash, tree, q);

(index,leaf,key_position)
}

fn dedup_fragment(idx:&mut[u32;16],val:&mut[[u8;32];16],mut d:usize,index:u32,leaf:[u8;32])->Result<usize,Error>{
for _ in 0..1 {
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
Ok(d)
}

fn padding_fragment<H:Digest32>(proof:&[u8],root:[u8;32],s:usize,idx:&mut[u32;16],val:&mut[[u8;32];16],d:usize,hash:H,count:usize)->Result<(),Error>{
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

fn padding_word_fragment(w:&[u8])->bool{u64::from_le_bytes(w.try_into().unwrap()) != 0}

// Entered parse-exit basic block; guard is derived separately, never assumed at a root.
fn parse_exit_fragment(_idx:&mut[u32;16],_val:&mut[[u8;32];16])->Result<(),Error>{
        return Err(Error::Parse);
}

fn scan_scalar_fragment(q:&[u8],s:usize,l:usize)->Result<(),Error>{
                M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
Ok(())
}

fn scan_c1_fragment(q:&[u8],s:usize)->Result<(),Error>{
            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
Ok(())
}

fn scan_c2_fragment(q:&[u8],s:usize,l:usize)->Result<(),Error>{
                K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?;
Ok(())
}

fn scan_echeck_fragment(q:&[u8])->Result<(),Error>{
        echeck(&q[672..800], false)?;
Ok(())
}

fn scan_prefix_fragment(proof:&[u8])->Result<(),Error>{
    compact::check_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE])?;
    echeck(&proof[compact::OFF_INACTIVE..compact::OFF_INACTIVE + 32], false)?;
    echeck(&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT], false)?;
    echeck(&proof[compact::OFF_ROUND1..compact::OFF_OPENINGS], false)?;
Ok(())
}
