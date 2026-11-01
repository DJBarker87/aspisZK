//! Fixed-width private witness boundary. No JSON witness or secret file paths.
use crate::diagnostics::{anyhow,ensure,err,Result};
use aspis_core::field::{M31,P};
use aspis_statement::poseidon2::Digest;
use std::{io::{Read,Write},path::Path};
use serde_json::Value;
pub const WIDTH:usize=212;
pub struct Wallet {
 pub input_key:Digest,pub input_salt:Digest,pub input_value:u64,pub asset:M31,
 pub change_key:Digest,pub change_salt:Digest,pub recipient_owner:Digest,
 pub recipient_salt:Digest,pub recipient_value:u64,pub record:[u8;WIDTH],
}
fn word(r:&[u8;WIDTH],i:usize)->u32{u32::from_le_bytes([r[i],r[i+1],r[i+2],r[i+3]])}
fn digest(r:&[u8;WIDTH],start:usize)->Digest{
 let mut out=[M31(0);8];let mut i=0;
 while i<8{out[i]=M31(word(r,start+4*i));i+=1;}out
}
fn long(r:&[u8;WIDTH],i:usize)->u64{word(r,i) as u64 | ((word(r,i+4) as u64)<<32)}
// Fixed offsets and fixed trip counts; content validity is checked separately.
#[inline(never)]
pub fn decode_wallet_record(r:&[u8;WIDTH])->Wallet{
 Wallet{input_key:digest(r,0),input_salt:digest(r,32),input_value:long(r,64),asset:M31(word(r,72)),
 change_key:digest(r,76),change_salt:digest(r,108),recipient_owner:digest(r,140),recipient_salt:digest(r,172),
 recipient_value:long(r,204),record:*r}
}
fn canonical_digest(d:Digest)->bool{
 let mut valid=true;let mut i=0;
 while i<8{valid &= d[i].0<P;i+=1;}valid
}
fn canonical(w:&Wallet)->bool{
 let mut valid=w.asset.0<P;
 valid &= canonical_digest(w.input_key);
 valid &= canonical_digest(w.input_salt);
 valid &= canonical_digest(w.change_key);
 valid &= canonical_digest(w.change_salt);
 valid &= canonical_digest(w.recipient_owner);
 valid &= canonical_digest(w.recipient_salt);
 valid
}
pub fn read(q:&Value)->Result<Wallet>{
 let fd=i32::try_from(crate::public_field(q,"wallet_bytes_fd").as_u64().ok_or_else(||anyhow!("missing wallet FD"))?).map_err(err)?;
 ensure!(fd>2,"wallet FD must be inherited separately from stdio");
 let mut channel=std::fs::File::open(format!("/proc/self/fd/{fd}")).map_err(err)?;
 let mut record=[0u8;WIDTH];channel.read_exact(&mut record).map_err(err)?;
 let mut tail=[0u8;1];ensure!(channel.read(&mut tail).map_err(err)?==0,"extra wallet bytes");
 let wallet=decode_wallet_record(&record);
 ensure!(canonical(&wallet),"noncanonical wallet field");Ok(wallet)
}
pub fn retain(dir:&Path,record:&[u8;WIDTH])->Result<()>{
 use std::os::unix::fs::OpenOptionsExt;
 let mut file=std::fs::OpenOptions::new().create_new(true).write(true).mode(0o600).open(crate::path_join(dir,"wallet-recovery.bin")).map_err(err)?;
 file.write_all(record).map_err(err)?;file.sync_all().map_err(err)?;Ok(())
}
