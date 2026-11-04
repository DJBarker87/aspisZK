use digest::core_api::{BlockSizeUser,BufferKindUser,CoreWrapper};
use digest::typenum::U64;
#[derive(Clone,Copy,Debug,Eq,PartialEq)] struct Core([u32;8]);
impl BlockSizeUser for Core {type BlockSize=U64;}
impl BufferKindUser for Core {type BufferKind=digest::block_buffer::Eager;}
struct Log {calls:usize,reply:Core,frame:[u32;8]}
// Full return type Core, arbitrary raw limbs. Modifies only calls/reply; frame preserved.
fn oracle(log:&mut Log)->Core {
 let reply=Core(kani::any());log.calls+=1;log.reply=reply;reply
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn wrapper_default_arbitrary_core() {
 let frame:[u32;8]=kani::any();let mut log=Log{calls:0,reply:Core([0;8]),frame};
 let native=CoreWrapper::<Core>::pv_context_default(|| oracle(&mut log));
 let (core,buffer)=native.decompose();
 let mut expected=log.reply;let mut bytes=[0u8;64];let mut pos=0;
 if cfg!(feature="negative-control") {
  let mode=crate::mutation();
  if mode<8 {expected.0[mode]^=1;}else if mode==8 {bytes[0]=1;}else if mode==9 {bytes[63]=1;}else if mode==10 {pos=1;}else {log.frame[0]^=1;}
 }
 assert_eq!(core,expected);assert_eq!(buffer.pv_dl_bytes(),&bytes);assert_eq!(buffer.get_pos(),pos);
 assert_eq!(log.calls,1);assert_eq!(log.frame,frame);
}
