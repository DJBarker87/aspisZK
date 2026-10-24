#![no_std]

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CodecError {
    Length,
    NonZeroHigh,
    NonCanonical,
}

#[inline(always)]
pub fn expand_values(compact: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
    if compact.len() % 16 != 0 || out.len() != 2 * compact.len() {
        return Err(CodecError::Length);
    }
    for (c, o) in compact.chunks_exact(16).zip(out.chunks_exact_mut(32)) {
        o[..16].copy_from_slice(c);
        o[16..].fill(0);
    }
    Ok(())
}

#[cfg(kani)]
mod proofs;

/// Proof-only owned reference: both complete buffers and the full codec result.
/// It introduces no digest/query calls and is not adopted production code.
pub fn y1_owned_reference(input:[u8;464],mut output:[u8;928])->(Result<(),CodecError>,[u8;928]) {
    let mut chunk=0usize;
    while chunk<29 {
        let mut byte=0usize;
        while byte<16 {
            output[chunk*32+byte]=input[chunk*16+byte];
            output[chunk*32+16+byte]=0;
            byte+=1;
        }
        chunk+=1;
    }
    (Ok(()),output)
}
