use digest::{Update,typenum::U64};
use digest::core_api::{BlockSizeUser,BufferKindUser,UpdateCore,Block,CoreWrapper};
use digest::block_buffer::{BlockBuffer,Eager};
#[path="default-reference.rs"] mod reference;
use reference::BatchCompression;
#[derive(Clone,Copy,Debug,Eq,PartialEq)]
struct Trace {events:[[u8;64];4],count:usize,groups:[usize;2],group_count:usize,blocks:u64}
struct Recording;
impl BatchCompression for Recording {
    type State=Trace;
    fn compress(mut s:Trace,bytes:&[u8])->Trace {
        let n=bytes.len()/64;s.groups[s.group_count]=n;s.group_count+=1;
        s.blocks=s.blocks.wrapping_add(n as u64);
        for i in 0..n {s.events[s.count].copy_from_slice(&bytes[64*i..64*(i+1)]);s.count+=1;}
        s
    }
}
struct Core {trace:Trace}
impl BlockSizeUser for Core {type BlockSize=U64;}
impl BufferKindUser for Core {type BufferKind=Eager;}
impl UpdateCore for Core {
    fn update_blocks(&mut self,blocks:&[Block<Self>]) {
        self.trace.groups[self.trace.group_count]=blocks.len();self.trace.group_count+=1;
        self.trace.blocks=self.trace.blocks.wrapping_add(blocks.len() as u64);
        for b in blocks {self.trace.events[self.trace.count].copy_from_slice(b);self.trace.count+=1;}
    }
}
#[test] fn native_batched_update_complete_state() {
    let mut cases=0;
    for pos in 0..64u8 {for seed in [0u8,1,127,255] {for n in 0..=193usize {for counter in [0,u64::MAX] {
        let bytes=core::array::from_fn(|i|seed.wrapping_add(i as u8));
        let input:[u8;193]=core::array::from_fn(|i|seed.rotate_left(i as u32).wrapping_sub(i as u8));
        let empty=Trace{events:[[0;64];4],count:0,groups:[0;2],group_count:0,blocks:counter};
        let mut native=CoreWrapper::pv_dl_from_parts(Core{trace:empty},
            BlockBuffer::<U64,Eager>::pv_dl_from_snapshot(bytes,pos));
        Update::update(&mut native,&input[..n]);
        let (core,buffer)=native.decompose();
        let (trace,retained,cursor)=reference::update_batch_reference::<Recording>(empty,bytes,pos as usize,&input[..n]);
        assert_eq!(core.trace,trace);assert_eq!(buffer.pv_dl_bytes(),retained.as_slice());assert_eq!(buffer.get_pos(),cursor);
        assert!(core.trace.group_count<=2);cases+=1;
    }}}}
    println!("{cases} paired native/batched-reference update cases; exact batches,counter,all64buffer bytes,cursor; finite validation only");
}
