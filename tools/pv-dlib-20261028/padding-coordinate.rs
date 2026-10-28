use digest::block_buffer::{BlockBuffer,Eager};
use digest::typenum::U64;
#[kani::proof]
#[kani::unwind(70)]
fn padding_events_coordinate() {
    let bytes:[u8;64]=kani::any();let pos:u8=kani::any();kani::assume(pos<64);
    let bit_len:u64=kani::any();
    let mut native=BlockBuffer::<U64,Eager>::pv_dl_from_snapshot(bytes,pos);
    let mut events=[[0;64];2];let mut count=0;
    native.len64_padding_be(bit_len,|b|{events[count].copy_from_slice(b);count+=1;});
    let (re,rc,_)=super::reference::padding_reference(bytes,pos as usize,bit_len);
    assert_eq!(count,rc);assert_eq!(native.get_pos(),0);
    let event:usize=kani::any();kani::assume(event<2);
    let byte:usize=kani::any();kani::assume(byte<64);
    assert_eq!(events[event][byte],re[event][byte]);
}
