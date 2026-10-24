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

// Proof-only owned byte operations. Moving the complete arrays through these
// helpers ends each indexing borrow inside the helper, before a loop edge.
#[inline(always)]
pub fn read_input(input:[u8;464],index:usize)->u8 { input[index] }
#[inline(always)]
pub fn write_output(mut output:[u8;928],index:usize,value:u8)->[u8;928] {
    output[index]=value;
    output
}
pub fn copy_chunk(input:[u8;464],mut output:[u8;928],chunk:usize)->[u8;928] {
    let mut byte=0usize;
    while byte<16 {
        let value=read_input(input,chunk*16+byte);
        output=write_output(output,chunk*32+byte,value);
        output=write_output(output,chunk*32+16+byte,0);
        byte+=1;
    }
    output
}
/// Complete source-reference result and both buffers; no production adoption.
pub fn y1_owned_reference(input:[u8;464],mut output:[u8;928])->(Result<(),CodecError>,[u8;928]) {
    let mut chunk=0usize;
    while chunk<29 {
        output=copy_chunk(input,output,chunk);
        chunk+=1;
    }
    (Ok(()),output)
}
