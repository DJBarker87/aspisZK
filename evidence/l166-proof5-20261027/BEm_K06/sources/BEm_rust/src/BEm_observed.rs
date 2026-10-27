// Caller owns the recorder across the batch cut, including backend entry.
fn observed_shipped<H:Digest32>(proof:&[u8],queries:[u32;22],roots:[[u8;32];3],ordinal:usize,backend:H,log:&RefCell<Vec<Attempt>>)->Result<(),Error> {
    shipped::batch_merkle_values(proof,queries,roots,ordinal,Recording{backend,log})
}
fn observed_reference<H:Digest32>(proof:&[u8],queries:[u32;22],roots:[[u8;32];3],ordinal:usize,backend:H,log:&RefCell<Vec<Attempt>>)->Result<(),Error> {
    batch(proof,queries,roots,ordinal,Recording{backend,log})
}
