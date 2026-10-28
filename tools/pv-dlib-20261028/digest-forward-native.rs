use digest::{Digest,FixedOutput,Output,HashMarker};
use digest::core_api::{CoreWrapper,FixedOutputCore,BlockSizeUser,BufferKindUser,
    OutputSizeUser,UpdateCore,Block,Buffer};
use digest::block_buffer::{BlockBuffer,Eager};
use digest::typenum::{U32,U64};
use std::{rc::Rc,cell::RefCell};
type Events=Rc<RefCell<Vec<(u8,u8)>>>;
struct Core {seed:[u8;32],events:Events}
impl Default for Core {fn default()->Self {Self{seed:[0;32],events:Rc::new(RefCell::new(Vec::new()))}}}
impl Drop for Core {fn drop(&mut self){self.events.borrow_mut().push((2,self.seed[0]));}}
impl HashMarker for Core {}
impl BlockSizeUser for Core {type BlockSize=U64;}
impl BufferKindUser for Core {type BufferKind=Eager;}
impl OutputSizeUser for Core {type OutputSize=U32;}
impl UpdateCore for Core {
    fn update_blocks(&mut self,blocks:&[Block<Self>]) {
        for b in blocks {for (i,byte) in b.iter().enumerate() {
            self.seed[i%32]=self.seed[i%32].wrapping_add(*byte);
        }}
    }
}
impl FixedOutputCore for Core {
    fn finalize_fixed_core(&mut self,buffer:&mut Buffer<Self>,out:&mut Output<Self>) {
        self.events.borrow_mut().push((1,self.seed[0]));
        let pos=buffer.get_pos() as u8;
        let head=if pos==0 {0}else{buffer.get_data()[0]};
        for i in 0..32 {out[i]=out[i].wrapping_add(self.seed[i]^pos).wrapping_add(head);}
        self.seed[0]^=1;buffer.reset();
    }
}
// Exact generic blanket delegation: overrides of finalize_fixed remain intact.
fn owned_digest<D:FixedOutput>(d:D)->Output<D> {FixedOutput::finalize_fixed(d)}
// Expanded inherited default method, used by the shipped CoreWrapper impl.
fn default_fixed<D:FixedOutput>(d:D)->Output<D> {
    let mut out=Default::default();FixedOutput::finalize_into(d,&mut out);out
}
fn owned_fixed(d:CoreWrapper<Core>,out:&mut Output<CoreWrapper<Core>>) {
    let (mut core,mut buffer)=d.decompose();
    core.finalize_fixed_core(&mut buffer,out);
}
fn run(seed:[u8;32],bytes:[u8;64],pos:u8,initial:[u8;32],mode:u8)->([u8;32],Vec<(u8,u8)>) {
    let events=Rc::new(RefCell::new(Vec::new()));
    let d=CoreWrapper::pv_dl_from_parts(Core{seed,events:Rc::clone(&events)},
        BlockBuffer::<U64,Eager>::pv_dl_from_snapshot(bytes,pos));
    let out=match mode {
        0=>Digest::finalize(d),
        1=>owned_digest(d),
        2=>default_fixed(d),
        3=>{let mut out=Output::<CoreWrapper<Core>>::clone_from_slice(&initial);
            FixedOutput::finalize_into(d,&mut out);out},
        4=>{let mut out=Output::<CoreWrapper<Core>>::clone_from_slice(&initial);
            owned_fixed(d,&mut out);out},
        _=>unreachable!()
    };
    assert_eq!(*events.borrow(),vec![(1,seed[0]),(2,seed[0]^1)]);
    let result=core::array::from_fn(|i|out[i]);let trace=events.borrow().clone();(result,trace)
}
#[test] fn native_digest_and_fixed_forwarding() {
    let mut count=0;
    for pos in 0..64u8 {for seed in [0u8,1,127,255] {
        let state=core::array::from_fn(|i|seed.wrapping_add(i as u8));
        let bytes=core::array::from_fn(|i|seed.rotate_left(i as u32).wrapping_add(i as u8));
        let initial=core::array::from_fn(|i|seed.wrapping_sub(i as u8));
        let native=run(state,bytes,pos,[0;32],0);
        let head=if pos==0 {0}else{bytes[0]};
        let expected:[u8;32]=core::array::from_fn(|i|(state[i]^pos).wrapping_add(head));
        assert_eq!(native.0,expected);
        assert_eq!(native,run(state,bytes,pos,[0;32],1));
        assert_eq!(native,run(state,bytes,pos,[0;32],2));
        assert_eq!(run(state,bytes,pos,initial,3),run(state,bytes,pos,initial,4));
        count+=1;
    }}
    println!("{count} same-input non-Copy Drop-core Digest triples and FixedOutput pairs; exact changed-state destructor trace; finite validation only");
}
