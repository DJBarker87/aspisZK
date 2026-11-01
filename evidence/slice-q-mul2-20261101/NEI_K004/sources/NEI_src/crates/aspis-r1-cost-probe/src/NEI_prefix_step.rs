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
fn NEI_prefix_iteration(flat:&[M31],prefixes:&mut Vec<M31>,product:&mut M31,index:&mut usize,log:&mut ProductLog){
    if *index<flat.len(){
        let value=flat[*index];
        prefixes.push(*product);
        *product=product_reply(log,*product,value);
        *index+=1;
    }
}
#[kani::proof] #[kani::unwind(444)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEI_copy::KMX_realloc)]
fn copy_window(){
    let source:[M31;110]=kani::any();let offset:usize=kani::any();kani::assume(offset<110);
    let old=source[offset].0;let destination=source;
    let expected=if cfg!(NEI_wrong_copy){old^1}else{old};
    assert_eq!(destination[offset].0,expected);
}
#[kani::proof] #[kani::unwind(8)]
fn allocation_capacity(){
    let length:usize=kani::any();kani::assume(length<=110);
    let vector:Vec<M31>=Vec::with_capacity(length);
    assert!(vector.len()==0);
    let expected=if cfg!(NEI_wrong_capacity){length+1}else{length};
    assert_eq!(vector.capacity(),expected);
}
#[kani::proof] #[kani::unwind(444)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEI_copy::KMX_realloc)]
fn prefix_window(){
    let length:usize=kani::any();let old_index:usize=kani::any();
    kani::assume(length<=110 && old_index<length);
    let mut flat=kani::vec::exact_vec::<M31,110>();flat.truncate(length);
    let mut prefixes=kani::vec::exact_vec::<M31,110>();prefixes.truncate(old_index);prefixes.shrink_to(length);
    assert_eq!(prefixes.capacity(),length);
    let old_product=M31(kani::any());let input=flat[old_index];
    let offset:usize=kani::any();kani::assume(offset<=old_index);
    let old_cell=if offset<old_index{prefixes[offset].0}else{old_product.0};
    let pointer=prefixes.as_ptr();let capacity=prefixes.capacity();
    let mut index=old_index;let mut product=old_product;
    let mut log=ProductLog{called:false,lhs:0,rhs:0,reply:0};
    NEI_prefix_iteration(&flat,&mut prefixes,&mut product,&mut index,&mut log);
    assert!(log.called && log.lhs==old_product.0 && log.rhs==input.0);
    assert!(index==old_index+1 && prefixes.len()==old_index+1);
    assert!(prefixes.as_ptr()==pointer && prefixes.capacity()==capacity);
    assert_eq!(prefixes[offset].0,old_cell);
    let expected=if cfg!(NEI_wrong_prefix){log.reply^1}else{log.reply};
    assert_eq!(product.0,expected);
}
