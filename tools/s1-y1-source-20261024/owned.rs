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
