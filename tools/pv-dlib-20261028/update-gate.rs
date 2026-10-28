use digest::core_api::{BlockSizeUser,BufferKindUser,UpdateCore,Block,CoreWrapper};
use digest::{Update,typenum::U64};
use super::reference::{self,Compression};
#[derive(Clone,Copy,Debug,Eq,PartialEq)]
struct Trace {events:[[u8;64];3],count:usize}
struct Recording;
impl Compression for Recording {
    type State=Trace;
    fn compress(mut s:Trace,b:[u8;64])->Trace {s.events[s.count]=b;s.count+=1;s}
}
#[derive(Clone,Copy)] struct Core {trace:Trace,blocks:u64}
impl BlockSizeUser for Core {type BlockSize=U64;}
impl BufferKindUser for Core {type BufferKind=digest::block_buffer::Eager;}
impl UpdateCore for Core {
    fn update_blocks(&mut self,blocks:&[Block<Self>]) {
        self.blocks=self.blocks.wrapping_add(blocks.len() as u64);
        for block in blocks {
            let mut b=[0;64];b.copy_from_slice(block);
            self.trace=Recording::compress(self.trace,b);
        }
    }
}
#[kani::proof]
#[kani::unwind(196)]
fn wrapper_update_events() {
    let prefix:[u8;64]=kani::any();let input:[u8;129]=kani::any();
    let p:usize=kani::any();kani::assume(p<64);
    let n:usize=kani::any();kani::assume(n<=129);
    let count:u64=kani::any();
    let empty=Trace{events:[[0;64];3],count:0};
    let mut native=CoreWrapper::from_core(Core{trace:empty,blocks:count});
    Update::update(&mut native,&prefix[..p]);
    Update::update(&mut native,&input[..n]);
    let (core,buffer)=native.decompose();
    let mut initial=[0;64];initial[..p].copy_from_slice(&prefix[..p]);
    let (rt,rc,rb,rp)=reference::update_reference::<Recording>(empty,count,initial,p,&input[..n]);
    assert_eq!(core.trace,rt);
    assert_eq!(core.blocks,rc);
    assert_eq!(buffer.get_pos(),rp);
    assert_eq!(buffer.get_data(),&rb[..rp]);
}
