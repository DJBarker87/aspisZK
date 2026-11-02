use std::io::{Error, ErrorKind};
use std::sync::{Arc, atomic::{AtomicUsize,Ordering}};
#[derive(Clone)] struct Payload(Arc<AtomicUsize>);
impl std::fmt::Display for Payload { fn fmt(&self,_:&mut std::fmt::Formatter<'_>)->std::fmt::Result { panic!("getter called Display") } }
impl std::fmt::Debug for Payload { fn fmt(&self,_:&mut std::fmt::Formatter<'_>)->std::fmt::Result { panic!("getter called Debug") } }
impl std::error::Error for Payload { fn source(&self)->Option<&(dyn std::error::Error+'static)> { panic!("getter called source") } }
impl Drop for Payload { fn drop(&mut self) { self.0.fetch_add(1,Ordering::SeqCst); } }
fn reference(n:i32)-> &'static str { match n {
 7=>"ArgumentListTooLong",98=>"AddrInUse",99=>"AddrNotAvailable",16=>"ResourceBusy",
 103=>"ConnectionAborted",111=>"ConnectionRefused",104=>"ConnectionReset",35=>"Deadlock",
 122=>"QuotaExceeded",17=>"AlreadyExists",27=>"FileTooLarge",113=>"HostUnreachable",
 4=>"Interrupted",22=>"InvalidInput",21=>"IsADirectory",40=>"FilesystemLoop",2=>"NotFound",
 12=>"OutOfMemory",28=>"StorageFull",38=>"Unsupported",31=>"TooManyLinks",36=>"InvalidFilename",
 100=>"NetworkDown",101=>"NetworkUnreachable",107=>"NotConnected",20=>"NotADirectory",
 39=>"DirectoryNotEmpty",32=>"BrokenPipe",30=>"ReadOnlyFilesystem",29=>"NotSeekable",
 116=>"StaleNetworkFileHandle",110=>"TimedOut",26=>"ExecutableFileBusy",18=>"CrossesDevices",
 115=>"InProgress",95=>"Unsupported",13|1=>"PermissionDenied",11=>"WouldBlock",_=>"Uncategorized" } }
fn main() {
 let mut os=0;
 for n in (-4096..=4096).chain([i32::MIN,i32::MAX]) {
  let e=Error::from_raw_os_error(n);let observed=format!("{:?}",e.kind());
  assert_eq!(observed,reference(n),"code {n}");assert_eq!(e.raw_os_error(),Some(n));os+=1;
 }
 let kinds=[ErrorKind::NotFound,ErrorKind::PermissionDenied,ErrorKind::ConnectionRefused,
 ErrorKind::ConnectionReset,ErrorKind::ConnectionAborted,ErrorKind::NotConnected,
 ErrorKind::AddrInUse,ErrorKind::AddrNotAvailable,ErrorKind::BrokenPipe,ErrorKind::AlreadyExists,
 ErrorKind::WouldBlock,ErrorKind::InvalidInput,ErrorKind::InvalidData,ErrorKind::TimedOut,
 ErrorKind::WriteZero,ErrorKind::Interrupted,ErrorKind::Unsupported,ErrorKind::UnexpectedEof,
 ErrorKind::OutOfMemory,ErrorKind::Other];
 let counter=Arc::new(AtomicUsize::new(0));
 for (i,k) in kinds.iter().copied().enumerate() {
  let simple=Error::from(k); assert_eq!(simple.kind(),k);
  let e=Error::new(k,Payload(counter.clone()));assert_eq!(e.kind(),k);
  assert_eq!(counter.load(Ordering::SeqCst),i); assert!(e.get_ref().is_some());drop(e);
  assert_eq!(counter.load(Ordering::SeqCst),i+1);
 }
 // A standard-library static-message error (invalid UTF-8 read_to_string).
 let e=std::io::read_to_string(std::io::Cursor::new([255u8])).unwrap_err();
 assert_eq!(e.kind(),ErrorKind::InvalidData); assert_eq!(e.raw_os_error(),None);
 // Matched native negative control is detected rather than silently accepted.
 assert_ne!(Error::from_raw_os_error(17).kind(),ErrorKind::NotFound);
 println!("os={os} simple={} custom={} static_message=1 no_payload_callbacks=true local_drops={} negative_control_detected=true",kinds.len(),kinds.len(),counter.load(Ordering::SeqCst));
}
