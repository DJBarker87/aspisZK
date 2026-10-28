#[kani::proof]
fn NBG_wide_writer_iteration(){
 let mut bytes:[u8;32]=kani::any();let before=bytes;let i:usize=kani::any();kani::assume(i<8);let limb:u32=kani::any();
 // One frozen chunks_exact_mut(4).zip(to_limbs()) iteration, arbitrary frame.
 let chunk=&mut bytes[4*i..4*i+4];chunk.copy_from_slice(&limb.to_le_bytes());
 let j:usize=kani::any();kani::assume(j<32);
 if j>=4*i&&j<4*i+4{assert!(bytes[j]==((limb>>(8*(j-4*i)))&255)as u8)}else{assert!(bytes[j]==before[j]);}
 kani::cover!(i==0&&j==31);
}
