// Safe references for the existing emitted field operations. No unsafe or Kani.
pub fn neg_ref(x:u32)->u32{if x==0{0}else{2147483647-x}}
pub fn canonical_ref(x:u32)->u32{x%2147483647}
pub fn cm_bytes_ref(a:u32,b:u32)->[u8;8]{[a as u8,(a>>8)as u8,(a>>16)as u8,(a>>24)as u8,b as u8,(b>>8)as u8,(b>>16)as u8,(b>>24)as u8]}
pub fn qm_bytes_ref(a:u32,b:u32,c:u32,d:u32)->[u8;16]{[a as u8,(a>>8)as u8,(a>>16)as u8,(a>>24)as u8,b as u8,(b>>8)as u8,(b>>16)as u8,(b>>24)as u8,c as u8,(c>>8)as u8,(c>>16)as u8,(c>>24)as u8,d as u8,(d>>8)as u8,(d>>16)as u8,(d>>24)as u8]}
