use digest::core_api::{BlockSizeUser,BufferKindUser,CoreWrapper};
use digest::block_buffer::Eager;
use digest::typenum::U64;
use std::cell::RefCell;
thread_local! {
    static SEED:RefCell<u64>=const{RefCell::new(0)};
    static TRACE:RefCell<Vec<(u8,u64)>>=const{RefCell::new(Vec::new())};
}
struct Core {value:u64}
impl BlockSizeUser for Core {type BlockSize=U64;}
impl BufferKindUser for Core {type BufferKind=Eager;}
impl Default for Core {
    fn default()->Self {
        let value=SEED.with(|s|*s.borrow());
        TRACE.with(|t|t.borrow_mut().push((1,value)));
        Self{value}
    }
}
impl Drop for Core {fn drop(&mut self){TRACE.with(|t|t.borrow_mut().push((2,self.value)));}}
fn one(seed:u64,owned:bool)->(u64,Vec<u8>,usize,Vec<(u8,u64)>) {
    SEED.with(|s|*s.borrow_mut()=seed);TRACE.with(|t|t.borrow_mut().clear());
    let wrapper=if owned {CoreWrapper::<Core>::pv_dl_owned_default()} else {CoreWrapper::<Core>::default()};
    TRACE.with(|t|assert_eq!(*t.borrow(),vec![(1,seed)]));
    let (core,buffer)=wrapper.decompose();
    let observed=(core.value,buffer.pv_dl_bytes().to_vec(),buffer.get_pos());
    assert_eq!(observed.0,seed);assert_eq!(observed.1,vec![0;64]);assert_eq!(observed.2,0);
    drop(core);
    let events=TRACE.with(|t|t.borrow().clone());assert_eq!(events,vec![(1,seed),(2,seed)]);
    (observed.0,observed.1,observed.2,events)
}
#[test] fn native_default_constructor() {
    for seed in [0,1,u64::MAX,0x123456789abcdef0] {
        assert_eq!(one(seed,false),one(seed,true));
    }
    println!("4 paired non-Copy Drop-core native/default-body constructor cases; core callback called exactly once,64zero bytes,pos0; finite validation only");
}
