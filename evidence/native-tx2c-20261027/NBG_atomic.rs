use super::*;
#[kani::proof]
fn NBG_unwrap_ok(){let x:u64=kani::any();assert!(super::unwrap_fixed_slice::<u64>(Ok(x))==x);kani::cover!(x==u64::MAX);}
#[kani::proof]
fn NBG_digest_decode(){
 let b:[u8;32]=kani::any();
 let words=[u32::from_le_bytes([b[0],b[1],b[2],b[3]]),u32::from_le_bytes([b[4],b[5],b[6],b[7]]),u32::from_le_bytes([b[8],b[9],b[10],b[11]]),u32::from_le_bytes([b[12],b[13],b[14],b[15]]),u32::from_le_bytes([b[16],b[17],b[18],b[19]]),u32::from_le_bytes([b[20],b[21],b[22],b[23]]),u32::from_le_bytes([b[24],b[25],b[26],b[27]]),u32::from_le_bytes([b[28],b[29],b[30],b[31]])];
 let canonical=words[0]<P&&words[1]<P&&words[2]<P&&words[3]<P&&words[4]<P&&words[5]<P&&words[6]<P&&words[7]<P;
 match super::decode_digest_canonical(&b){Err(e)=>{assert!(e==AtomicStatementError::NonCanonicalDigest);assert!(!canonical);},Ok(d)=>{assert!(canonical);let i:usize=kani::any();kani::assume(i<8);assert!(d[i].0==words[i]);}}
 kani::cover!(words[7]==P);
}
#[kani::proof]
fn NBG_encode_digest_step(){
 let mut bytes:[u8;32]=kani::any();let before=bytes;
 let index:usize=kani::any();kani::assume(index<8);let value=M31(kani::any());
 // Verbatim frozen iteration body on arbitrary pre-state.
 bytes[index*4..index*4+4].copy_from_slice(&value.to_le_bytes());
 let j:usize=kani::any();kani::assume(j<32);
 if j>=index*4&&j<index*4+4{assert!(bytes[j]==((value.0>>(8*(j-index*4)))&255)as u8)}else{assert!(bytes[j]==before[j]);}
 kani::cover!(index==7&&j==31);
}
