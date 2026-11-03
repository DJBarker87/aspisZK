//! Fixed-width private witness boundary. No JSON witness or secret file paths.
use crate::diagnostics::{anyhow,ensure,err,Result};
use aspis_core::field::{M31,P};
use aspis_statement::poseidon2::Digest;
use std::io::Write;
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
fn long(r:&[u8;WIDTH],i:usize)->u64{word(r,i) as u64 | ((word(r,i+4) as u64)<<32u32)}
// Fixed offsets and fixed trip counts; content validity is checked separately.
#[inline(never)]
pub fn decode_wallet_record(r:&[u8;WIDTH])->Wallet{
 Wallet{input_key:digest(r,0),input_salt:digest(r,32),input_value:long(r,64),asset:M31(word(r,72)),
 change_key:digest(r,76),change_salt:digest(r,108),recipient_owner:digest(r,140),recipient_salt:digest(r,172),
 recipient_value:long(r,204),record:*r}
}
fn canonical_digest(d:Digest)->bool{
 (d[0].0<P) & (d[1].0<P) & (d[2].0<P) & (d[3].0<P) & (d[4].0<P) & (d[5].0<P) & (d[6].0<P) & (d[7].0<P)
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
 let mut channel=crate::wallet_open_channel(crate::wallet_fd_path(fd))?;
 let record=crate::wallet_read_record(&mut channel)?;
 let decoded=decode_wallet_record(&record);
 ensure!(canonical(&decoded),"noncanonical wallet field");Ok(decoded)
}
// The calling wallet owns persistence. This endpoint accepts a distinct inherited
// writable pipe only; regular files, sockets and stdio are rejected before a write.
pub fn output_channel(q:&Value)->Result<std::fs::File>{
 use std::os::{fd::{BorrowedFd},unix::fs::{FileTypeExt,MetadataExt}};
 unsafe extern "C" { fn fcntl(fd:i32,cmd:i32,...) -> i32; }
 let fd=i32::try_from(crate::public_field(q,"wallet_output_fd").as_u64().ok_or_else(||anyhow!("missing wallet output FD"))?).map_err(err)?;
 let input=crate::public_field(q,"wallet_bytes_fd").as_u64().ok_or_else(||anyhow!("missing wallet FD"))?;
 ensure!(fd>2 && fd as u64!=input,"wallet output must be separate from input and stdio");
 // borrow_raw requires a valid descriptor; validate with F_GETFL before borrowing.
 let flags=unsafe{fcntl(fd,3)};
 ensure!(flags>=0 && flags & 3==1,"wallet output must be write-only");
 let owned=unsafe{BorrowedFd::borrow_raw(fd)}.try_clone_to_owned().map_err(err)?;
 let file=std::fs::File::from(owned);
 let target=file.metadata().map_err(err)?;
 ensure!(target.file_type().is_fifo(),"wallet output must be a pipe");
 // Different descriptor numbers can still name one pipe. Reject aliases of
 // stdio and the private input channel before reading any witness bytes.
 for other in [0,1,2,i32::try_from(input).map_err(err)?]{
  if unsafe{fcntl(other,3)}>=0{
   let borrowed=unsafe{BorrowedFd::borrow_raw(other)}.try_clone_to_owned().map_err(err)?;
   let metadata=std::fs::File::from(borrowed).metadata().map_err(err)?;
   ensure!(target.dev()!=metadata.dev() || target.ino()!=metadata.ino(),"wallet output must be a separate pipe");
  }
 }
 Ok(file)
}
pub fn return_record(channel:&mut std::fs::File,record:&[u8;WIDTH])->Result<()>{
 channel.write_all(record).map_err(err)
}
