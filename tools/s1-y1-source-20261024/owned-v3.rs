extern crate alloc;
use alloc::vec::Vec;

// Complete owned buffers move through helpers; indexing borrows end before
// loop edges. No byte, result variant or error-frame data is projected away.
#[inline(always)]
pub fn read_input(input:Vec<u8>,index:usize)->(u8,Vec<u8>) {
    let value=input[index];
    (value,input)
}
#[inline(always)]
pub fn write_output(mut output:Vec<u8>,index:usize,value:u8)->Vec<u8> {
    output[index]=value;
    output
}
pub fn copy_chunk(mut input:Vec<u8>,mut output:Vec<u8>,chunk:usize)->(Vec<u8>,Vec<u8>) {
    let mut byte=0usize;
    while byte<16 {
        let (value,next)=read_input(input,chunk*16+byte);
        input=next;
        output=write_output(output,chunk*32+byte,value);
        output=write_output(output,chunk*32+16+byte,0);
        byte+=1;
    }
    (input,output)
}
/// Proof-only complete owned reference. The original guard order, checked
/// arithmetic and full input/output/result carriers are retained.
pub fn values_owned_reference(mut input:Vec<u8>,mut output:Vec<u8>)->(Result<(),CodecError>,Vec<u8>,Vec<u8>) {
    if input.len()%16!=0 || output.len()!=2*input.len() {
        return (Err(CodecError::Length),input,output);
    }
    let count=input.len()/16;
    let mut chunk=0usize;
    while chunk<count {
        let (next_input,next_output)=copy_chunk(input,output,chunk);
        input=next_input;
        output=next_output;
        chunk+=1;
    }
    (Ok(()),input,output)
}
