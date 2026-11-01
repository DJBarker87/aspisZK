#[path="default-reference.rs"] mod reference;
use block_buffer::{BlockBuffer,Eager};
use block_buffer::generic_array::typenum::U64;
#[derive(Clone,Copy,Debug,Eq,PartialEq)]
struct Trace { events:[[u8;64];3],count:usize }
struct Recording;
impl reference::Compression for Recording {
    type State=Trace;
    fn compress(mut s:Trace,b:[u8;64])->Trace {
        s.events[s.count]=b;s.count+=1;s
    }
}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(196)]
fn eager_update_events() {
    let prefix:[u8;64]=kani::any();
    let data:[u8;129]=kani::any();
    let p:usize=kani::any();kani::assume(p<64);
    let n:usize=kani::any();kani::assume(n<=129);
    let mut native=BlockBuffer::<U64,Eager>::new(&prefix[..p]);
    let mut initial=[0u8;64];initial[..p].copy_from_slice(&prefix[..p]);
    let empty=Trace{events:[[0;64];3],count:0};
    let mut trace=empty;
    native.digest_blocks(&data[..n],|blocks| {
        for block in blocks {
            let mut b=[0;64];b.copy_from_slice(block);
            trace=Recording::compress(trace,b);
        }
    });
    let (rt,rb,rbuf,rp)=reference::update_reference::<Recording>(empty,0,initial,p,&data[..n]);
    assert_eq!(trace,rt);
    assert_eq!(rb,rt.count as u64);
    assert_eq!(native.get_pos(),rp);
    assert_eq!(native.get_data(),&rbuf[..rp]);
}
use reference::Compression;
