use digest::{Digest,FixedOutput,HashMarker,Output,Update};
use digest::core_api::{BlockSizeUser,BufferKindUser,CoreWrapper,CtVariableCoreWrapper,
    FixedOutputCore,OutputSizeUser,UpdateCore,VariableOutputCore,Block,Buffer,TruncSide};
use digest::typenum::{U28,U32,U64};
use digest::block_buffer::{BlockBuffer,Eager};
#[derive(Clone,Copy,Default)] struct Fixed {value:[u8;32]}
impl BlockSizeUser for Fixed {type BlockSize=U64;}
impl BufferKindUser for Fixed {type BufferKind=Eager;}
impl OutputSizeUser for Fixed {type OutputSize=U32;}
impl HashMarker for Fixed {}
impl UpdateCore for Fixed {fn update_blocks(&mut self,_:&[Block<Self>]) {}}
impl FixedOutputCore for Fixed {
    fn finalize_fixed_core(&mut self,buffer:&mut Buffer<Self>,out:&mut Output<Self>) {
        let p=buffer.get_pos() as u8;
        for j in 0..32 {out[j]=self.value[j]^p;}
        if p!=0 {out[0]^=buffer.get_data()[0];}
        self.value[0]^=1;buffer.reset();
    }
}
static mut SEED:[u8;32]=[0;32];
#[derive(Clone,Copy)] struct Variable<const RIGHT:bool> {value:[u8;32]}
impl<const R:bool> BlockSizeUser for Variable<R> {type BlockSize=U64;}
impl<const R:bool> BufferKindUser for Variable<R> {type BufferKind=Eager;}
impl<const R:bool> OutputSizeUser for Variable<R> {type OutputSize=U32;}
impl<const R:bool> UpdateCore for Variable<R> {fn update_blocks(&mut self,_:&[Block<Self>]) {}}
impl<const R:bool> VariableOutputCore for Variable<R> {
    const TRUNC_SIDE:TruncSide=if R {TruncSide::Right} else {TruncSide::Left};
    fn new(n:usize)->Result<Self,digest::InvalidOutputSize> {
        if n<=32 {Ok(Self{value:unsafe{SEED}})} else {Err(digest::InvalidOutputSize)}
    }
    fn finalize_variable_core(&mut self,buffer:&mut Buffer<Self>,out:&mut Output<Self>) {
        let p=buffer.get_pos() as u8;
        for j in 0..32 {out[j]=self.value[j]^p;}
        if p!=0 {out[0]^=buffer.get_data()[0];}
        self.value[0]^=1;buffer.reset();
    }
}
#[kani::proof]
#[kani::unwind(70)]
fn finalize_truncate_and_retained() {
    let seed:[u8;32]=kani::any();let bytes:[u8;64]=kani::any();
    let pos:u8=kani::any();kani::assume(pos<64);
    let bit_len:u64=kani::any();
    let byte:usize=kani::any();kani::assume(byte<64);
    let mut padded=BlockBuffer::<U64,Eager>::pv_dl_from_snapshot(bytes,pos);
    let mut events=[[0;64];2];let mut count=0;
    padded.len64_padding_be(bit_len,|b|{events[count].copy_from_slice(b);count+=1;});
    let (re,rc,retained)=super::retained_reference::padding_retained_reference(bytes,pos as usize,bit_len);
    let event:usize=kani::any();kani::assume(event<2);
    assert_eq!(events[event][byte],re[event][byte]);assert_eq!(count,rc);
    assert_eq!(padded.pv_dl_bytes()[byte],retained[byte]);assert_eq!(padded.get_pos(),0);
    let mut expected=seed;
    for j in 0..32 {expected[j]^=pos;}
    if pos!=0 {expected[0]^=bytes[0];}
    let make=||CoreWrapper::pv_dl_from_parts(Fixed{value:seed},
        BlockBuffer::pv_dl_from_snapshot(bytes,pos));
    let index:usize=kani::any();kani::assume(index<32);
    let got=Digest::finalize(make());assert_eq!(got[index],expected[index]);
    let mut out:Output<CoreWrapper<Fixed>>=Default::default();
    FixedOutput::finalize_into(make(),&mut out);assert_eq!(out[index],expected[index]);
    unsafe{SEED=seed;}
    macro_rules! check_ct {($r:literal,$size:ty,$n:expr,$start:expr)=>{{
        let mut core:CtVariableCoreWrapper<Variable<$r>,$size>=Default::default();
        let mut buffer=BlockBuffer::pv_dl_from_snapshot(bytes,pos);
        let mut out:Output<CtVariableCoreWrapper<Variable<$r>,$size>>=Default::default();
        FixedOutputCore::finalize_fixed_core(&mut core,&mut buffer,&mut out);
        let k:usize=kani::any();kani::assume(k<$n);
        assert_eq!(out[k],expected[k+$start]);
        assert_eq!(core.pv_dl_inner().value[0],seed[0]^1);
        assert_eq!(buffer.get_pos(),0);
    }}}
    check_ct!(false,U28,28,0);check_ct!(true,U28,28,4);check_ct!(false,U32,32,0);
    assert!(!core::mem::needs_drop::<sha2::Sha256>());
}
