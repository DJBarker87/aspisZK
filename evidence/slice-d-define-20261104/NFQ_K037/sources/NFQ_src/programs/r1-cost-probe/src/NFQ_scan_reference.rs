// Total safe scalar/scan references; the scan is proved by induction.
pub fn readonly_buffer_ref(signer:bool,writable:bool,executable:bool)->bool{!(signer||writable||executable)}
pub fn zero_step_ref(byte:u8)->bool{byte==0}
pub fn zero_ref(bytes:&[u8])->bool{
 let mut i=0;let mut all=true;
 while i<bytes.len() && all {all=bytes[i]==0;i+=1;}all
}
