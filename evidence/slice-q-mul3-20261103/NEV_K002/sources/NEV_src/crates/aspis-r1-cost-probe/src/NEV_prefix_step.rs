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
#[kani::proof] #[kani::unwind(8)]
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

// Arbitrary valid prestate, built at fixed offsets. This is setup only.
// No fixed capacity, initialized-word restriction, custom allocator, or loop body.
#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_push_fixed_offsets() {
 let length:usize=kani::any();let index:usize=kani::any();
 kani::assume(length<=110 && index<length);
 let mut before:Vec<M31>=Vec::with_capacity(length);
 assert_eq!(before.capacity(),length);
 let initialized=before.as_mut_ptr();
 if 0<index {unsafe {initialized.add(0).write(M31(kani::any()));}}
 if 1<index {unsafe {initialized.add(1).write(M31(kani::any()));}}
 if 2<index {unsafe {initialized.add(2).write(M31(kani::any()));}}
 if 3<index {unsafe {initialized.add(3).write(M31(kani::any()));}}
 if 4<index {unsafe {initialized.add(4).write(M31(kani::any()));}}
 if 5<index {unsafe {initialized.add(5).write(M31(kani::any()));}}
 if 6<index {unsafe {initialized.add(6).write(M31(kani::any()));}}
 if 7<index {unsafe {initialized.add(7).write(M31(kani::any()));}}
 if 8<index {unsafe {initialized.add(8).write(M31(kani::any()));}}
 if 9<index {unsafe {initialized.add(9).write(M31(kani::any()));}}
 if 10<index {unsafe {initialized.add(10).write(M31(kani::any()));}}
 if 11<index {unsafe {initialized.add(11).write(M31(kani::any()));}}
 if 12<index {unsafe {initialized.add(12).write(M31(kani::any()));}}
 if 13<index {unsafe {initialized.add(13).write(M31(kani::any()));}}
 if 14<index {unsafe {initialized.add(14).write(M31(kani::any()));}}
 if 15<index {unsafe {initialized.add(15).write(M31(kani::any()));}}
 if 16<index {unsafe {initialized.add(16).write(M31(kani::any()));}}
 if 17<index {unsafe {initialized.add(17).write(M31(kani::any()));}}
 if 18<index {unsafe {initialized.add(18).write(M31(kani::any()));}}
 if 19<index {unsafe {initialized.add(19).write(M31(kani::any()));}}
 if 20<index {unsafe {initialized.add(20).write(M31(kani::any()));}}
 if 21<index {unsafe {initialized.add(21).write(M31(kani::any()));}}
 if 22<index {unsafe {initialized.add(22).write(M31(kani::any()));}}
 if 23<index {unsafe {initialized.add(23).write(M31(kani::any()));}}
 if 24<index {unsafe {initialized.add(24).write(M31(kani::any()));}}
 if 25<index {unsafe {initialized.add(25).write(M31(kani::any()));}}
 if 26<index {unsafe {initialized.add(26).write(M31(kani::any()));}}
 if 27<index {unsafe {initialized.add(27).write(M31(kani::any()));}}
 if 28<index {unsafe {initialized.add(28).write(M31(kani::any()));}}
 if 29<index {unsafe {initialized.add(29).write(M31(kani::any()));}}
 if 30<index {unsafe {initialized.add(30).write(M31(kani::any()));}}
 if 31<index {unsafe {initialized.add(31).write(M31(kani::any()));}}
 if 32<index {unsafe {initialized.add(32).write(M31(kani::any()));}}
 if 33<index {unsafe {initialized.add(33).write(M31(kani::any()));}}
 if 34<index {unsafe {initialized.add(34).write(M31(kani::any()));}}
 if 35<index {unsafe {initialized.add(35).write(M31(kani::any()));}}
 if 36<index {unsafe {initialized.add(36).write(M31(kani::any()));}}
 if 37<index {unsafe {initialized.add(37).write(M31(kani::any()));}}
 if 38<index {unsafe {initialized.add(38).write(M31(kani::any()));}}
 if 39<index {unsafe {initialized.add(39).write(M31(kani::any()));}}
 if 40<index {unsafe {initialized.add(40).write(M31(kani::any()));}}
 if 41<index {unsafe {initialized.add(41).write(M31(kani::any()));}}
 if 42<index {unsafe {initialized.add(42).write(M31(kani::any()));}}
 if 43<index {unsafe {initialized.add(43).write(M31(kani::any()));}}
 if 44<index {unsafe {initialized.add(44).write(M31(kani::any()));}}
 if 45<index {unsafe {initialized.add(45).write(M31(kani::any()));}}
 if 46<index {unsafe {initialized.add(46).write(M31(kani::any()));}}
 if 47<index {unsafe {initialized.add(47).write(M31(kani::any()));}}
 if 48<index {unsafe {initialized.add(48).write(M31(kani::any()));}}
 if 49<index {unsafe {initialized.add(49).write(M31(kani::any()));}}
 if 50<index {unsafe {initialized.add(50).write(M31(kani::any()));}}
 if 51<index {unsafe {initialized.add(51).write(M31(kani::any()));}}
 if 52<index {unsafe {initialized.add(52).write(M31(kani::any()));}}
 if 53<index {unsafe {initialized.add(53).write(M31(kani::any()));}}
 if 54<index {unsafe {initialized.add(54).write(M31(kani::any()));}}
 if 55<index {unsafe {initialized.add(55).write(M31(kani::any()));}}
 if 56<index {unsafe {initialized.add(56).write(M31(kani::any()));}}
 if 57<index {unsafe {initialized.add(57).write(M31(kani::any()));}}
 if 58<index {unsafe {initialized.add(58).write(M31(kani::any()));}}
 if 59<index {unsafe {initialized.add(59).write(M31(kani::any()));}}
 if 60<index {unsafe {initialized.add(60).write(M31(kani::any()));}}
 if 61<index {unsafe {initialized.add(61).write(M31(kani::any()));}}
 if 62<index {unsafe {initialized.add(62).write(M31(kani::any()));}}
 if 63<index {unsafe {initialized.add(63).write(M31(kani::any()));}}
 if 64<index {unsafe {initialized.add(64).write(M31(kani::any()));}}
 if 65<index {unsafe {initialized.add(65).write(M31(kani::any()));}}
 if 66<index {unsafe {initialized.add(66).write(M31(kani::any()));}}
 if 67<index {unsafe {initialized.add(67).write(M31(kani::any()));}}
 if 68<index {unsafe {initialized.add(68).write(M31(kani::any()));}}
 if 69<index {unsafe {initialized.add(69).write(M31(kani::any()));}}
 if 70<index {unsafe {initialized.add(70).write(M31(kani::any()));}}
 if 71<index {unsafe {initialized.add(71).write(M31(kani::any()));}}
 if 72<index {unsafe {initialized.add(72).write(M31(kani::any()));}}
 if 73<index {unsafe {initialized.add(73).write(M31(kani::any()));}}
 if 74<index {unsafe {initialized.add(74).write(M31(kani::any()));}}
 if 75<index {unsafe {initialized.add(75).write(M31(kani::any()));}}
 if 76<index {unsafe {initialized.add(76).write(M31(kani::any()));}}
 if 77<index {unsafe {initialized.add(77).write(M31(kani::any()));}}
 if 78<index {unsafe {initialized.add(78).write(M31(kani::any()));}}
 if 79<index {unsafe {initialized.add(79).write(M31(kani::any()));}}
 if 80<index {unsafe {initialized.add(80).write(M31(kani::any()));}}
 if 81<index {unsafe {initialized.add(81).write(M31(kani::any()));}}
 if 82<index {unsafe {initialized.add(82).write(M31(kani::any()));}}
 if 83<index {unsafe {initialized.add(83).write(M31(kani::any()));}}
 if 84<index {unsafe {initialized.add(84).write(M31(kani::any()));}}
 if 85<index {unsafe {initialized.add(85).write(M31(kani::any()));}}
 if 86<index {unsafe {initialized.add(86).write(M31(kani::any()));}}
 if 87<index {unsafe {initialized.add(87).write(M31(kani::any()));}}
 if 88<index {unsafe {initialized.add(88).write(M31(kani::any()));}}
 if 89<index {unsafe {initialized.add(89).write(M31(kani::any()));}}
 if 90<index {unsafe {initialized.add(90).write(M31(kani::any()));}}
 if 91<index {unsafe {initialized.add(91).write(M31(kani::any()));}}
 if 92<index {unsafe {initialized.add(92).write(M31(kani::any()));}}
 if 93<index {unsafe {initialized.add(93).write(M31(kani::any()));}}
 if 94<index {unsafe {initialized.add(94).write(M31(kani::any()));}}
 if 95<index {unsafe {initialized.add(95).write(M31(kani::any()));}}
 if 96<index {unsafe {initialized.add(96).write(M31(kani::any()));}}
 if 97<index {unsafe {initialized.add(97).write(M31(kani::any()));}}
 if 98<index {unsafe {initialized.add(98).write(M31(kani::any()));}}
 if 99<index {unsafe {initialized.add(99).write(M31(kani::any()));}}
 if 100<index {unsafe {initialized.add(100).write(M31(kani::any()));}}
 if 101<index {unsafe {initialized.add(101).write(M31(kani::any()));}}
 if 102<index {unsafe {initialized.add(102).write(M31(kani::any()));}}
 if 103<index {unsafe {initialized.add(103).write(M31(kani::any()));}}
 if 104<index {unsafe {initialized.add(104).write(M31(kani::any()));}}
 if 105<index {unsafe {initialized.add(105).write(M31(kani::any()));}}
 if 106<index {unsafe {initialized.add(106).write(M31(kani::any()));}}
 if 107<index {unsafe {initialized.add(107).write(M31(kani::any()));}}
 if 108<index {unsafe {initialized.add(108).write(M31(kani::any()));}}
 if 109<index {unsafe {initialized.add(109).write(M31(kani::any()));}}

 unsafe {before.set_len(index);}
 let pointer=before.as_ptr();let product=M31(kani::any());
 before.push(product);
 let appended=unsafe {before.as_ptr().add(index).read()}.0;
 assert_eq!(appended,if cfg!(NEV_wrong_fixed_offsets){product.0^1}else{product.0});
 assert!(before.len()==index+1 && before.capacity()==length && before.as_ptr()==pointer);
}
