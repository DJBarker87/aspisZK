fn merkle_exit_fragment(_idx:&mut[u32;16],_val:&mut[[u8;32];16])->Result<(),Error>{
return Err(Error::Merkle);
}

fn ok_exit_fragment(_idx:&mut[u32;16],_val:&mut[[u8;32];16])->Result<(),Error>{
Ok(())
}
