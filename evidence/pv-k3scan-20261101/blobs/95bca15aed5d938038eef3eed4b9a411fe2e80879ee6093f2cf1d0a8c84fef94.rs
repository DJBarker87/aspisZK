use digest::core_api::{BlockSizeUser,BufferKindUser,UpdateCore,Block,CoreWrapper};
use digest::{Update,typenum::U64};
use super::reference::{self,BatchCompression};
#[derive(Clone,Copy,Debug,Eq,PartialEq)]
struct Trace {events:[[u8;64];3],count:usize,groups:[usize;2],group_count:usize,blocks:u64}
struct Recording;
impl BatchCompression for Recording {
    type State=Trace;
    fn compress(mut s:Trace,bytes:&[u8])->Trace {
        let n=bytes.len()/64;
        s.groups[s.group_count]=n;s.group_count+=1;
        s.blocks=s.blocks.wrapping_add(n as u64);
        let mut i=0;
        while i<n {
            s.events[s.count].copy_from_slice(&bytes[64*i..64*(i+1)]);
            s.count+=1;i+=1;
        }
        s
    }
}
#[derive(Clone,Copy)] struct Core {trace:Trace}
impl BlockSizeUser for Core {type BlockSize=U64;}
impl BufferKindUser for Core {type BufferKind=digest::block_buffer::Eager;}
impl UpdateCore for Core {
    fn update_blocks(&mut self,blocks:&[Block<Self>]) {
        self.trace.groups[self.trace.group_count]=blocks.len();self.trace.group_count+=1;
        self.trace.blocks=self.trace.blocks.wrapping_add(blocks.len() as u64);
        for block in blocks {
            self.trace.events[self.trace.count].copy_from_slice(block);
            self.trace.count+=1;
        }
    }
}
#[kani::proof]
#[kani::unwind(70)]
fn wrapper_update_coordinate() {
    let bytes:[u8;64]=kani::any();let input:[u8;129]=kani::any();
    let p:u8=kani::any();kani::assume(p<64);
    let n:usize=kani::any();kani::assume(n<=129);
    let count:u64=kani::any();
    let empty=Trace{events:[[0;64];3],count:0,groups:[0;2],group_count:0,blocks:count};
    let buffer=digest::block_buffer::BlockBuffer::pv_dl_from_snapshot(bytes,p);
    let mut native=CoreWrapper::pv_dl_from_parts(Core{trace:empty},buffer);
    Update::update(&mut native,&input[..n]);
    let (core,buffer)=native.decompose();
    let (rt,rb,rp)=reference::update_batch_reference::<Recording>(empty,bytes,p as usize,&input[..n]);
    assert_eq!(core.trace.count,rt.count);
    assert_eq!(core.trace.group_count,rt.group_count);
    assert_eq!(core.trace.groups,rt.groups);
    assert_eq!(core.trace.blocks,rt.blocks);
    assert_eq!(buffer.get_pos(),rp);
    let event:usize=kani::any();kani::assume(event<3);
    let byte:usize=kani::any();kani::assume(byte<64);
    assert_eq!(core.trace.events[event][byte],rt.events[event][byte]);
    assert_eq!(buffer.pv_dl_bytes()[byte],rb[byte]);
}
