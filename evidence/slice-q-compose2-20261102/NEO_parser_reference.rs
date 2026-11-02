pub const MODULUS:u32=2147483647;
pub fn m_ref(b:[u8;4])->Option<u32> {let v=u32::from_le_bytes(b);if v<MODULUS{Some(v)}else{None}}
pub fn limbs_ref(x:[u32;8])->Option<[u32;8]> {
 if x[0]>=MODULUS||x[1]>=MODULUS||x[2]>=MODULUS||x[3]>=MODULUS||x[4]>=MODULUS||x[5]>=MODULUS||x[6]>=MODULUS||x[7]>=MODULUS{None}else{Some(x)}
}
