fn merkle_exit_fragment(_idx:&mut[u32;16],_val:&mut[[u8;32];16])->Result<(),Error>{
return Err(Error::Merkle);
}

fn ok_exit_fragment(_idx:&mut[u32;16],_val:&mut[[u8;32];16])->Result<(),Error>{
Ok(())
}

fn verify_finish_fragment<H:Digest32>(root:[u8;32],idx:&mut[u32;16],val:&mut[[u8;32];16],d:usize,nodes:&[u8],count:usize,hash:H)->Result<(),Error>{
    if !multiproof::verify_in_place(hash, Arity::Two, &root, idx, val, d, &nodes[..32 * count]) {
        return Err(Error::Merkle);
    }
    Ok(())
}

fn capacity_fragment<H:Digest32>(proof:&[u8],root:[u8;32],s:usize,idx:&mut[u32;16],val:&mut[[u8;32];16],d:usize,hash:H,count:usize)->Result<(),Error>{
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
fn count_input_fragment(idx:&[u32;16],d:usize)->&[u32]{ &idx[..d] }
