use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn encode_spec(root:&Digest)->[u8;32] {
    let w0=root[0].0.to_le_bytes();
    let w1=root[1].0.to_le_bytes();
    let w2=root[2].0.to_le_bytes();
    let w3=root[3].0.to_le_bytes();
    let w4=root[4].0.to_le_bytes();
    let w5=root[5].0.to_le_bytes();
    let w6=root[6].0.to_le_bytes();
    let w7=root[7].0.to_le_bytes();
    [w0[0], w0[1], w0[2], w0[3], w1[0], w1[1], w1[2], w1[3], w2[0], w2[1], w2[2], w2[3], w3[0], w3[1], w3[2], w3[3], w4[0], w4[1], w4[2], w4[3], w5[0], w5[1], w5[2], w5[3], w6[0], w6[1], w6[2], w6[3], w7[0], w7[1], w7[2], w7[3]]
}
// One exact source-ordered geometry step, history.rs:276-277.
#[kani::requires(offset<256 && usize::from(filled)+offset<256)]
#[cfg_attr(not(PCB_NEG_GEOM),kani::ensures(|r| *r==64+(usize::from(filled)+offset)*32))]
#[cfg_attr(PCB_NEG_GEOM,kani::ensures(|r| *r!=64+(usize::from(filled)+offset)*32))]
fn geometry(filled:u16,offset:usize)->usize {
    let slot=usize::from(filled)+offset;
    let start=PAGE_ROOTS_OFFSET+slot*32;
    start
}
#[kani::proof_for_contract(geometry)]
fn geometry_contract(){let filled:u16=kani::any();let offset:usize=kani::any();kani::assume(offset<256 && usize::from(filled)+offset<256);let _=geometry(filled,offset);}
// Borrowed destination is precisely data[start..start+32], not a whole page.
#[kani::modifies(window)]
#[cfg_attr(not(PCB_NEG_WINDOW),kani::ensures(|_| *window==*encoded))]
#[cfg_attr(PCB_NEG_WINDOW,kani::ensures(|_| window[0]!=encoded[0]))]
fn write_window(window:&mut [u8;32],encoded:&[u8;32]) {
    window.copy_from_slice(encoded);
}
#[kani::proof_for_contract(write_window)] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_contract(){let encoded:[u8;32]=kani::any();let mut window:[u8;32]=kani::any();write_window(&mut window,&encoded);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_control(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<32);dst.copy_from_slice(&src);
 #[cfg(not(PCB_NEG_COPY))] assert_eq!(dst[j],src[j]);
 #[cfg(PCB_NEG_COPY)] assert_ne!(dst[j],src[j]);
}
