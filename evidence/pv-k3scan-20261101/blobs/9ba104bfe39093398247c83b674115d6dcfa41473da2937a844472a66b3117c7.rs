use digest::{Output,InvalidOutputSize};
use digest::core_api::{BlockSizeUser,BufferKindUser,OutputSizeUser,UpdateCore,VariableOutputCore,
    FixedOutputCore,CtVariableCoreWrapper,Block,Buffer,TruncSide};
use digest::block_buffer::{BlockBuffer,Eager};
use digest::typenum::{U28,U32,U64};
use std::cell::RefCell;
thread_local!{static SEED:RefCell<[u8;32]>=const{RefCell::new([0;32])};}
struct Variable<const R:bool> {value:[u8;32]}
impl<const R:bool> BlockSizeUser for Variable<R> {type BlockSize=U64;}
impl<const R:bool> BufferKindUser for Variable<R> {type BufferKind=Eager;}
impl<const R:bool> OutputSizeUser for Variable<R> {type OutputSize=U32;}
impl<const R:bool> UpdateCore for Variable<R> {
    fn update_blocks(&mut self,blocks:&[Block<Self>]) {
        for b in blocks {for (i,x) in b.iter().enumerate() {
            self.value[i%32]=self.value[i%32].wrapping_add(*x);
        }}
    }
}
impl<const R:bool> VariableOutputCore for Variable<R> {
    const TRUNC_SIDE:TruncSide=if R {TruncSide::Right}else{TruncSide::Left};
    fn new(n:usize)->Result<Self,InvalidOutputSize> {
        if n<=32 {Ok(Self{value:SEED.with(|s|*s.borrow())})} else {Err(InvalidOutputSize)}
    }
    fn finalize_variable_core(&mut self,buffer:&mut Buffer<Self>,out:&mut Output<Self>) {
        let pos=buffer.get_pos() as u8;
        let head=if pos==0 {0}else{buffer.get_data()[0]};
        for i in 0..32 {out[i]=out[i].wrapping_add(self.value[i]^pos).wrapping_add(head);}
        self.value[0]^=1;
        let changed=core::array::from_fn(|i|buffer.pv_dl_bytes()[i]^0x5a);
        *buffer=BlockBuffer::pv_dl_from_snapshot(changed,0);
    }
}
macro_rules! run {
    ($right:literal,$size:ty,$n:expr,$begin:expr,$seed:expr,$bytes:expr,$pos:expr,$owned:expr)=>{{
        SEED.with(|s|*s.borrow_mut()=$seed);
        let mut core:CtVariableCoreWrapper<Variable<$right>,$size>=Default::default();
        let mut buffer=BlockBuffer::<U64,Eager>::pv_dl_from_snapshot($bytes,$pos);
        let mut out:Output<CtVariableCoreWrapper<Variable<$right>,$size>>=Default::default();
        if $owned {core.pv_dl_owned_finalize_fixed_core(&mut buffer,&mut out);}
        else {FixedOutputCore::finalize_fixed_core(&mut core,&mut buffer,&mut out);}
        let head=if $pos==0 {0}else{$bytes[0]};
        let full:[u8;32]=core::array::from_fn(|i|($seed[i]^$pos).wrapping_add(head));
        assert_eq!(out.as_slice(),&full[$begin..$begin+$n]);
        assert_eq!(core.pv_dl_inner().value[0],$seed[0]^1);
        let changed:[u8;64]=core::array::from_fn(|i|$bytes[i]^0x5a);
        assert_eq!(buffer.pv_dl_bytes(),changed.as_slice());assert_eq!(buffer.get_pos(),0);
        (out.to_vec(),core.pv_dl_inner().value,buffer.pv_dl_bytes().to_vec())
    }}
}
#[test] fn native_ct_complete_restoration() {
    let mut count=0;
    for pos in 0..64u8 {for value in [0u8,1,127,255] {
        let seed:[u8;32]=core::array::from_fn(|i|value.wrapping_add(i as u8));
        let bytes:[u8;64]=core::array::from_fn(|i|value.wrapping_sub(i as u8));
        assert_eq!(run!(false,U28,28,0,seed,bytes,pos,false),run!(false,U28,28,0,seed,bytes,pos,true));
        assert_eq!(run!(true,U28,28,4,seed,bytes,pos,false),run!(true,U28,28,4,seed,bytes,pos,true));
        assert_eq!(run!(false,U32,32,0,seed,bytes,pos,false),run!(false,U32,32,0,seed,bytes,pos,true));
        assert_eq!(run!(true,U32,32,0,seed,bytes,pos,false),run!(true,U32,32,0,seed,bytes,pos,true));
        count+=4;
    }}
    println!("{count} paired native/owned Ct cases; left/right28/32, changed core, all64buffer bytes restored; finite validation only");
}
