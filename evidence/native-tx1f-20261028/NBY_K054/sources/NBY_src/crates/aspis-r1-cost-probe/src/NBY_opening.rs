use super::*;
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_reborrow_load(){let a:[u8;32]=kani::any();let start:usize=kani::any();let len:usize=kani::any();let k:usize=kani::any();kani::assume(start<=32&&len<=32-start&&k<len);let q=&a[start..start+len];let p=q.as_ptr();let x=q[k];assert!(x==a[start+k]&&p==a.as_ptr().wrapping_add(start));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_reborrow_load_wrong(){let a:[u8;32]=kani::any();let start:usize=kani::any();let len:usize=kani::any();let k:usize=kani::any();kani::assume(start<=32&&len<=32-start&&k<len);let q=&a[start..start+len];let p=q.as_ptr();let x=q[k];assert!(!(x==a[start+k]&&p==a.as_ptr().wrapping_add(start)));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_reborrow_nested(){let a:[u8;32]=kani::any();let start:usize=kani::any();let end:usize=kani::any();let offset:usize=kani::any();let k:usize=kani::any();kani::assume(start<=end&&end<=32&&offset<=end-start&&k<end-start-offset);let q=&a[start..end];let r=&q[offset..];assert!(r[k]==a[start+offset+k]&&r.len()==end-start-offset);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_reborrow_nested_wrong(){let a:[u8;32]=kani::any();let start:usize=kani::any();let end:usize=kani::any();let offset:usize=kani::any();let k:usize=kani::any();kani::assume(start<=end&&end<=32&&offset<=end-start&&k<end-start-offset);let q=&a[start..end];let r=&q[offset..];assert!(!(r[k]==a[start+offset+k]&&r.len()==end-start-offset));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_reborrow_read_frame(){let a:[u8;32]=kani::any();let j:usize=kani::any();let k:usize=kani::any();let begin:usize=kani::any();kani::assume(begin<32&&j<32-begin&&k<32);let before=a[k];let q=&a[begin..];let read=q[j];assert!(a[k]==before&&read==a[begin+j]);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_reborrow_read_frame_wrong(){let a:[u8;32]=kani::any();let j:usize=kani::any();let k:usize=kani::any();let begin:usize=kani::any();kani::assume(begin<32&&j<32-begin&&k<32);let before=a[k];let q=&a[begin..];let read=q[j];assert!(!(a[k]==before&&read==a[begin+j]));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_load8(){let a:[u8;32]=kani::any();let start:usize=kani::any();let k:usize=kani::any();kani::assume(start<=24&&k<8);let q=&a[start..start+8];assert!(q[k]==a[start+k]);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_load8_wrong(){let a:[u8;32]=kani::any();let start:usize=kani::any();let k:usize=kani::any();kani::assume(start<=24&&k<8);let q=&a[start..start+8];assert!(!(q[k]==a[start+k]));}
