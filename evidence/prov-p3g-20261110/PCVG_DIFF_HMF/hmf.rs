fn main(){ let mut acc:u64=0; for x in 0u32..65536 { let v=(x as u16).count_ones() as u64*32+(x as u16).trailing_zeros() as u64; acc=acc.wrapping_mul(1000003).wrapping_add(v);} println!("{}",acc); }
