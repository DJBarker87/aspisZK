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
