include!("BEm_owned.rs");
include!("BEm_observed.rs");

// The identical generic backend and caller-owned log remain explicit operands.
pub(crate) fn extracted_shipped<H:Digest32>(proof:&[u8],queries:[u32;22],roots:[[u8;32];3],ordinal:usize,backend:H,log:&RefCell<Vec<Attempt>>)->Result<(),Error> {
    observed_shipped(proof,queries,roots,ordinal,backend,log)
}
pub(crate) fn extracted_reference<H:Digest32>(proof:&[u8],queries:[u32;22],roots:[[u8;32];3],ordinal:usize,backend:H,log:&RefCell<Vec<Attempt>>)->Result<(),Error> {
    observed_reference(proof,queries,roots,ordinal,backend,log)
}
