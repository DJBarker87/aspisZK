// Conditional decoder cut: exact selected window and unchanged Some reply.
// This does not establish the real decoder's value/success law.
static mut NDD_BYTES:[u8;64]=[0;64];
static mut NDD_INDEX:usize=0;
static mut NDD_REPLY:E=E::ZERO;
fn decode_cut(bytes:&[u8])->Option<E>{
 assert_eq!(bytes.len(),32);let k:usize=kani::any();kani::assume(k<32);
 let expected=unsafe{NDD_BYTES[NDD_INDEX*32+k]};
 if cfg!(NDD_negative_selector){assert_ne!(bytes[k],expected);}else{assert_eq!(bytes[k],expected);}
 Some(unsafe{NDD_REPLY})
}
#[kani::proof]
#[kani::stub(aspis_core::field::WideExact::from_le_bytes,decode_cut)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn field_selector_cut(){let bytes:[u8;64]=kani::any();let i:usize=kani::any();kani::assume(i<2);
 let reply=E::new(q(),q());unsafe{NDD_BYTES=bytes;NDD_INDEX=i;NDD_REPLY=reply;}
 assert_eq!(field(&bytes,i),reply);
}
