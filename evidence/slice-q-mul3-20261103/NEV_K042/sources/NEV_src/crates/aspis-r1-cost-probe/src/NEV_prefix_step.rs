use super::*;
#[derive(Clone,Copy)]
struct ProductLog { called:bool, lhs:u32, rhs:u32, reply:u32 }
// Over-approximation only: actual product specialization is proved in Lean.
fn product_reply(log:&mut ProductLog,lhs:M31,rhs:M31)->M31 {
    assert!(!log.called);
    let reply:u32=kani::any();kani::assume(reply<2147483647);
    *log=ProductLog{called:true,lhs:lhs.0,rhs:rhs.0,reply};M31(reply)
}
// One frozen prefix iteration; the multiplication call alone is abstracted.
fn NEV_prefix_iteration(flat:&[M31],prefixes:&mut Vec<M31>,product:&mut M31,index:&mut usize,log:&mut ProductLog){
    if *index<flat.len(){
        let value=flat[*index];
        prefixes.push(*product);
        *product=product_reply(log,*product,value);
        *index+=1;
    }
}
#[kani::proof] #[kani::unwind(444)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn copy_window(){
    let source:[M31;110]=kani::any();let offset:usize=kani::any();kani::assume(offset<110);
    let old=source[offset].0;let destination=source;
    let expected=if cfg!(NEV_wrong_copy){old^1}else{old};
    assert_eq!(destination[offset].0,expected);
}
#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn allocation_capacity(){
    let length:usize=kani::any();kani::assume(length<=110);
    let vector:Vec<M31>=Vec::with_capacity(length);
    assert!(vector.len()==0);
    let expected=if cfg!(NEV_wrong_capacity){length+1}else{length};
    assert_eq!(vector.capacity(),expected);
}
#[kani::proof] #[kani::unwind(444)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_window(){
    let length:usize=kani::any();let old_index:usize=kani::any();
    kani::assume(length<=110 && old_index<length);
    // Arbitrary flat state; initialization is not a verifier iteration.
    let storage:[M31;110]=kani::any();let flat=&storage[..length];
    let mut prefixes:Vec<M31>=Vec::with_capacity(length);
    // Initialize a valid arbitrary Vec prestate without a bulk realloc/copy.
    for _ in 0..old_index { prefixes.push(M31(kani::any())); }
    assert_eq!(prefixes.capacity(),length);
    let old_product=M31(kani::any());let input=flat[old_index];
    let offset:usize=kani::any();kani::assume(offset<=old_index);
    let old_cell=if offset<old_index{prefixes[offset].0}else{old_product.0};
    let flat_offset:usize=kani::any();kani::assume(flat_offset<length);
    let flat_cell=flat[flat_offset].0;
    let pointer=prefixes.as_ptr();let capacity=prefixes.capacity();
    let mut index=old_index;let mut product=old_product;
    let mut log=ProductLog{called:false,lhs:0,rhs:0,reply:0};
    NEV_prefix_iteration(&flat,&mut prefixes,&mut product,&mut index,&mut log);
    assert!(log.called && log.lhs==old_product.0 && log.rhs==input.0);
    assert!(index==old_index+1 && prefixes.len()==old_index+1);
    assert!(prefixes.as_ptr()==pointer && prefixes.capacity()==capacity);
    assert_eq!(prefixes[offset].0,old_cell);
    assert_eq!(flat[flat_offset].0,flat_cell);
    let expected=if cfg!(NEV_wrong_prefix){log.reply^1}else{log.reply};
    assert_eq!(product.0,expected);
}

// Split cut 1: actual read / abstract product-call log / checked index update.
#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn prefix_read_log(){
    let length:usize=kani::any();let old_index:usize=kani::any();kani::assume(length<=110 && old_index<length);
    let storage:[M31;110]=kani::any();let flat=&storage[..length];
    let mut index=old_index;let old_product=M31(kani::any());let mut product=old_product;
    let input=flat[index];let mut log=ProductLog{called:false,lhs:0,rhs:0,reply:0};
    let value=flat[index];product=product_reply(&mut log,product,value);index+=1;
    assert!(log.called && log.lhs==old_product.0 && product.0==log.reply && index==old_index+1);
    let expected=if cfg!(NEV_wrong_read){input.0^1}else{input.0};
    assert_eq!(log.rhs,expected);
}
// Split cut 2: one arbitrary destination position of the ACTUAL Vec<M31>::push.
#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_append_window(){
    let length:usize=kani::any();let old_index:usize=kani::any();kani::assume(length<=110 && old_index<length);
    // This creates every logical prefix prestate at the actual requested capacity,
    // with a typed M31 copy rather than a byte-wise realloc or repeated pushes.
    let mut donor=kani::vec::exact_vec::<M31,110>();
    let mut prefixes=donor.split_off(110-length);prefixes.truncate(old_index);
    assert_eq!(prefixes.capacity(),length);assert_eq!(prefixes.len(),old_index);
    let product=M31(kani::any());let offset:usize=kani::any();kani::assume(offset<=old_index);
    let old_cell=if offset<old_index{prefixes[offset].0}else{product.0};
    let pointer=prefixes.as_ptr();let capacity=prefixes.capacity();
    prefixes.push(product);
    assert!(prefixes.len()==old_index+1 && prefixes.capacity()==capacity && prefixes.as_ptr()==pointer);
    let expected=if cfg!(NEV_wrong_append){old_cell^1}else{old_cell};
    assert_eq!(prefixes[offset].0,expected);
}

// New split after K005/K006/K009: no observation or duplicate copy of the
// existing prefix. Only actual no-growth push geometry and the written cell.
#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_append_geometry() {
 let length:usize=kani::any();let index:usize=kani::any();kani::assume(length<=110 && index<length);
 let mut before:Vec<M31>=Vec::with_capacity(length);
 assert_eq!(before.capacity(),length);
 // Valid arbitrary pre-state: initialize EVERY live word before set_len.
 // index<length=capacity, M31 is a plain u32 wrapper, spare words stay uninit.
 let initialized=before.as_mut_ptr();
 for at in 0..index {unsafe {initialized.add(at).write(M31(kani::any()));}}
 unsafe {before.set_len(index);}
 assert!(before.len()==index && before.capacity()==length);
 let pointer=before.as_ptr();let product=M31(kani::any());
 before.push(product);
 assert!(before.len()==index+1 && before.capacity()==length && before.as_ptr()==pointer);
 assert_eq!(before[index].0,if cfg!(NEV_wrong_push_geometry){product.0^1}else{product.0});
}
// Primitive write/frame on one actual M31[110] location. No whole-array copy.
#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn prefix_word_write_frame() {
 let mut storage=kani::vec::exact_vec::<M31,110>();let index:usize=kani::any();let observed:usize=kani::any();
 kani::assume(index<110 && observed<110);
 let before=storage[observed].0;let replacement=M31(kani::any());
 let pointer=storage.as_mut_ptr();unsafe {pointer.add(index).write(replacement);}
 let expected=if index==observed{replacement.0}else{before};
 assert_eq!(storage[observed].0,if cfg!(NEV_wrong_word_frame){expected^1}else{expected});
}

// Separate metadata and direct appended-cell observations; timed-out original
// prefix_append_geometry stays unchanged and uncredited.

#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_metadata_geometry() {
 // Negative control isolates the valid length=1,index=0 counterexample.
 // The positive configuration retains the full arbitrary-prestate domain.
 let length:usize=if cfg!(NEV_wrong_prefix_metadata){1}else{kani::any()};
 let index:usize=if cfg!(NEV_wrong_prefix_metadata){0}else{kani::any()};
 kani::assume(length<=110 && index<length);
 let mut before:Vec<M31>=Vec::with_capacity(length);
 assert_eq!(before.capacity(),length);
 // Valid arbitrary pre-state: initialize EVERY live word before set_len.
 // index<length=capacity, M31 is a plain u32 wrapper, spare words stay uninit.
 let initialized=before.as_mut_ptr();
 for at in 0..index {unsafe {initialized.add(at).write(M31(kani::any()));}}
 unsafe {before.set_len(index);}
 assert!(before.len()==index && before.capacity()==length);
 let pointer=before.as_ptr();let product=M31(kani::any());
 before.push(product);
 // One postcondition per configuration. Negative control falsifies actual length,
 // rather than solving the full positive postcondition before a second assertion.
 if cfg!(NEV_wrong_prefix_metadata) {assert!(before.len()!=index+1);} else {
  assert!(before.len()==index+1 && before.capacity()==length && before.as_ptr()==pointer);
 }
}

#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_append_cell() {
 let length:usize=if cfg!(NEV_wrong_prefix_cell){1}else{kani::any()};
 let index:usize=if cfg!(NEV_wrong_prefix_cell){0}else{kani::any()};
 kani::assume(length<=110 && index<length);
 let mut before:Vec<M31>=Vec::with_capacity(length);
 assert_eq!(before.capacity(),length);
 // Valid arbitrary pre-state: initialize EVERY live word before set_len.
 // index<length=capacity, M31 is a plain u32 wrapper, spare words stay uninit.
 let initialized=before.as_mut_ptr();
 for at in 0..index {unsafe {initialized.add(at).write(M31(kani::any()));}}
 unsafe {before.set_len(index);}
 assert!(before.len()==index && before.capacity()==length);
 let pointer=before.as_ptr();let product=M31(kani::any());
 before.push(product);

 let appended=unsafe{before.as_ptr().add(index).read()};
 assert_eq!(appended.0,if cfg!(NEV_wrong_prefix_cell){product.0^1}else{product.0});
}

// An independent old-word observation after the ACTUAL push; metadata and the
// appended word are checked separately. Positive inputs remain fully arbitrary.
#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_old_word_frame() {
 let length:usize=if cfg!(NEV_wrong_prefix_old){2}else{kani::any()};
 let index:usize=if cfg!(NEV_wrong_prefix_old){1}else{kani::any()};
 let observed:usize=if cfg!(NEV_wrong_prefix_old){0}else{kani::any()};
 kani::assume(length<=110 && index<length && observed<index);
 let mut before:Vec<M31>=Vec::with_capacity(length);
 assert_eq!(before.capacity(),length);
 let initialized=before.as_mut_ptr();
 for at in 0..index {unsafe {initialized.add(at).write(M31(kani::any()));}}
 unsafe {before.set_len(index);}
 assert!(before.len()==index && before.capacity()==length);
 let old=before[observed].0;let product=M31(kani::any());
 before.push(product);
 let after=unsafe{before.as_ptr().add(observed).read()}.0;
 assert_eq!(after,if cfg!(NEV_wrong_prefix_old){old^1}else{old});
}
// Exact Kani arbitrary initialized allocation. Truncation only drops u32 wrappers.
fn NEV_append_fixed_capacity<const CAP:usize>() {
 let mut before=kani::vec::exact_vec::<M31,CAP>();
 let index:usize=kani::any();let observed:usize=kani::any();
 kani::assume(index<CAP && observed<=index);
 before.truncate(index);
 let product=M31(kani::any());let old=if observed<index{before[observed].0}else{product.0};
 let pointer=before.as_ptr();
 before.push(product);
 let after=before[observed].0;
 assert_eq!(after,if cfg!(NEV_wrong_fixed_offsets){old^1}else{old});
 assert!(before.len()==index+1 && before.capacity()==CAP && before.as_ptr()==pointer);
}
#[kani::proof] #[kani::unwind(444)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_push_fixed_offsets() {
 let length:usize=kani::any();
 kani::assume(100<=length && length<=105 && (length-100)%5==0);
 match length {
 100=>NEV_append_fixed_capacity::<100>(),
 105=>NEV_append_fixed_capacity::<105>(),
 _=>unreachable!(),
 }
}
