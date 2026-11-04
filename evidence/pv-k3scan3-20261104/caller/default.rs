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
 let expected=if cfg!(feature="negative-control") {Core([log.reply.0[0]^1,log.reply.0[1],log.reply.0[2],log.reply.0[3],log.reply.0[4],log.reply.0[5],log.reply.0[6],log.reply.0[7]])} else {log.reply};
 assert_eq!(core,expected);assert_eq!(buffer.pv_dl_bytes(),&[0;64]);assert_eq!(buffer.get_pos(),0);
 assert_eq!(log.calls,1);assert_eq!(log.frame,frame);
}
