use digest::block_buffer::{BlockBuffer,Eager};
use digest::typenum::U64;
#[kani::proof]
#[kani::unwind(70)]
fn padding_events() {
    let bytes:[u8;64]=kani::any();let pos:usize=kani::any();kani::assume(pos<64);
    let bit_len:u64=kani::any();
    let mut native=BlockBuffer::<U64,Eager>::new(&bytes[..pos]);
    let mut events=[[0;64];2];let mut count=0;
    native.len64_padding_be(bit_len,|b|{events[count].copy_from_slice(b);count+=1;});
    let (re,rc,_)=super::reference::padding_reference(bytes,pos,bit_len);
    assert_eq!(events,re);assert_eq!(count,rc);assert_eq!(native.get_pos(),0);
}
