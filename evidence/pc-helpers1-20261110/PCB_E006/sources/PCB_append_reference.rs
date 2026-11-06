#[derive(Clone,Copy)]
pub struct M31(pub u32);
pub type Digest=[M31;8];
pub fn encode_spec(root:&Digest)->[u8;32] {
    let w0=root[0].0.to_le_bytes();
    let w1=root[1].0.to_le_bytes();
    let w2=root[2].0.to_le_bytes();
    let w3=root[3].0.to_le_bytes();
    let w4=root[4].0.to_le_bytes();
    let w5=root[5].0.to_le_bytes();
    let w6=root[6].0.to_le_bytes();
    let w7=root[7].0.to_le_bytes();
    [w0[0], w0[1], w0[2], w0[3], w1[0], w1[1], w1[2], w1[3], w2[0], w2[1], w2[2], w2[3], w3[0], w3[1], w3[2], w3[3], w4[0], w4[1], w4[2], w4[3], w5[0], w5[1], w5[2], w5[3], w6[0], w6[1], w6[2], w6[3], w7[0], w7[1], w7[2], w7[3]]
}
pub fn geometry(filled:u16,offset:usize)->usize {
 let slot=usize::from(filled)+offset;
 let start=64+slot*32;
 start
}
pub fn filled_bytes(filled:u16,count:usize)->[u8;2] {
 let filled=filled+count as u16;
 filled.to_le_bytes()
}
