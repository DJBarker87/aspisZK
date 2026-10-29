use std::io::{self, Write};
use std::panic::{catch_unwind, AssertUnwindSafe};
#[derive(Default)] struct Writer { bytes: Vec<u8>, calls: usize, left: usize, mode: u8 }
impl Write for Writer {
 fn write(&mut self, b: &[u8]) -> io::Result<usize> {
  self.calls+=1;
  if self.mode==1 && self.calls==1 { return Err(io::ErrorKind::Interrupted.into()); }
  if self.left==0 {
   if self.mode==2 { panic!("controlled writer panic"); }
   return Err(io::ErrorKind::Other.into());
  }
  let n=b.len().min(self.left).min(2); self.bytes.extend_from_slice(&b[..n]); self.left-=n; Ok(n)
 }
 fn flush(&mut self)->io::Result<()> {Ok(())}
}
fn main() {
 std::panic::set_hook(Box::new(|_|{}));
 for mode in 0..=2 {
  let mut w=Writer{left:3,mode,..Default::default()};
  let out=catch_unwind(AssertUnwindSafe(|| w.write_all(b"abcdef")));
  assert_eq!(w.bytes,b"abc");
  if mode==2 { assert!(out.is_err()); } else { assert!(out.unwrap().is_err()); }
  assert_eq!(w.calls,if mode==1 {4} else {3});
 }
 let mut w=Writer{left:4,..Default::default()};
 let dynamic="abcdef";
 assert!(write!(&mut w,"{}:{}",dynamic,17).is_err());
 assert_eq!(w.bytes,b"abcd");
 println!("4 finite controls passed; partial delivery survives error/Interrupted/panic/dynamic format");
}
