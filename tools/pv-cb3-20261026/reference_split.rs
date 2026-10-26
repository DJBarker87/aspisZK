//! Owned safe reference with named straight-line stages; cfg(kani)-only parent.
use aspis_core::field::{QM31,CM31,M31,WideExact,P};
pub fn words(block:[u8;32])->[u32;8] {
    [
        u32::from_le_bytes([block[0],block[1],block[2],block[3]]),
        u32::from_le_bytes([block[4],block[5],block[6],block[7]]),
        u32::from_le_bytes([block[8],block[9],block[10],block[11]]),
        u32::from_le_bytes([block[12],block[13],block[14],block[15]]),
        u32::from_le_bytes([block[16],block[17],block[18],block[19]]),
        u32::from_le_bytes([block[20],block[21],block[22],block[23]]),
        u32::from_le_bytes([block[24],block[25],block[26],block[27]]),
        u32::from_le_bytes([block[28],block[29],block[30],block[31]]),
    ]
}
pub fn word_step(word:u32,remainder:u64)->(u32,u64) {
    let dividend=(remainder<<32)|u64::from(word);
    ((dividend/u64::from(P)) as u32, dividend%u64::from(P))
}
pub fn pass(rank:[u32;8])->([u32;8],u32) {
    let (q7,r1)=word_step(rank[7],0);
    let (q6,r2)=word_step(rank[6],r1);
    let (q5,r3)=word_step(rank[5],r2);
    let (q4,r4)=word_step(rank[4],r3);
    let (q3,r5)=word_step(rank[3],r4);
    let (q2,r6)=word_step(rank[2],r5);
    let (q1,r7)=word_step(rank[1],r6);
    let (q0,r8)=word_step(rank[0],r7);
    ([q0,q1,q2,q3,q4,q5,q6,q7],r8 as u32)
}
pub fn carry_step(digit:u32,addend:u32)->(u32,u32) {
    let sum=u64::from(digit)+u64::from(addend);
    ((sum%u64::from(P)) as u32,(sum/u64::from(P)) as u32)
}
pub fn carry(digits:[u32;8],addend:u32)->([u32;8],bool) {
    let (d0,c1)=carry_step(digits[0],addend);
    let (d1,c2)=carry_step(digits[1],c1);
    let (d2,c3)=carry_step(digits[2],c2);
    let (d3,c4)=carry_step(digits[3],c3);
    let (d4,c5)=carry_step(digits[4],c4);
    let (d5,c6)=carry_step(digits[5],c5);
    let (d6,c7)=carry_step(digits[6],c6);
    let (d7,c8)=carry_step(digits[7],c7);
    ([d0,d1,d2,d3,d4,d5,d6,d7],c8!=0)
}
pub fn gamma(block:[u8;32])->WideExact {
    let rank0=words(block);
    let (rank1,d0)=pass(rank0);
    let (rank2,d1)=pass(rank1);
    let (rank3,d2)=pass(rank2);
    let (rank4,d3)=pass(rank3);
    let (rank5,d4)=pass(rank4);
    let (rank6,d5)=pass(rank5);
    let (rank7,d6)=pass(rank6);
    let (rank8,d7)=pass(rank7);
    let (digits,wrapped)=carry([d0,d1,d2,d3,d4,d5,d6,d7],rank8[0]+1);
    let digits=if wrapped {carry(digits,1).0}else{digits};
    WideExact::new(QM31{c0:CM31{a:M31(digits[0]),b:M31(digits[1])},c1:CM31{a:M31(digits[2]),b:M31(digits[3])}},
        QM31{c0:CM31{a:M31(digits[4]),b:M31(digits[5])},c1:CM31{a:M31(digits[6]),b:M31(digits[7])}})
}
