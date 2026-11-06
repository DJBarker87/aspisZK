#[derive(Default)]
struct ScanCallLog{calls:usize,ptr:usize,len:usize,flag:bool,reply_ok:bool}
fn arbitrary_echeck(_: &[u8],_:bool)->Result<(),Error>{if kani::any(){Ok(())}else{Err(Error::Parse)}}
fn arbitrary_compact(_: &[u8])->Result<(),CodecError>{if kani::any(){Ok(())}else{Err(CodecError::NonCanonical)}}
// Source-ordered call-boundary template: materialize the child reply once,
// log it, then execute the frozen question-mark propagation.
fn scan_echeck_call(bytes:&[u8],log:&mut ScanCallLog)->Result<(),Error>{
 log.calls+=1;log.ptr=bytes.as_ptr()as usize;log.len=bytes.len();log.flag=false;
 let reply=echeck(bytes,false);log.reply_ok=reply.is_ok();reply?;Ok(())
}
fn scan_compact_call(bytes:&[u8],log:&mut ScanCallLog)->Result<(),Error>{
 log.calls+=1;log.ptr=bytes.as_ptr()as usize;log.len=bytes.len();
 let reply=compact::check_values(bytes);log.reply_ok=reply.is_ok();reply?;Ok(())
}
#[kani::proof]
#[kani::unwind(2)]
#[kani::stub(super::echeck,arbitrary_echeck)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn scan_echeck_call_cut(){
 let bytes:[u8;2272]=kani::any();let len:usize=kani::any();kani::assume(len<=2272);let input=&bytes[..len];let mut log=ScanCallLog::default();
 let out=scan_echeck_call(input,&mut log);assert_eq!(out.is_ok(),log.reply_ok);if !log.reply_ok{assert!(matches!(out,Err(Error::Parse)))}
 assert_eq!(log.ptr,input.as_ptr()as usize);assert_eq!(log.len,len);assert!(!log.flag);
 #[cfg(not(NKL_invert))] assert_eq!(log.calls,1);
 #[cfg(NKL_invert)] assert_ne!(log.calls,1);
}
#[kani::proof]
#[kani::unwind(2)]
#[kani::stub(compact::check_values,arbitrary_compact)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn scan_compact_call_cut(){
 let bytes:[u8;464]=kani::any();let len:usize=kani::any();kani::assume(len<=464);let input=&bytes[..len];let mut log=ScanCallLog::default();
 let out=scan_compact_call(input,&mut log);assert_eq!(out.is_ok(),log.reply_ok);if !log.reply_ok{assert!(matches!(out,Err(Error::Parse)))}
 assert_eq!(log.ptr,input.as_ptr()as usize);assert_eq!(log.len,len);
 #[cfg(not(NKL_invert))] assert_eq!(log.calls,1);
 #[cfg(NKL_invert)] assert_ne!(log.calls,1);
}
