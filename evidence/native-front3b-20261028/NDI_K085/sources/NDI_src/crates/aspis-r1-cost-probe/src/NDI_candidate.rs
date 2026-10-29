use super::*;
#[path="NDI_reference.rs"] mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::requires(lo<=22 && n<=16 && lo+n<=22 && j<n && tree<3)]
#[kani::modifies(&mut keys[j])]
#[kani::ensures(|_| (keys[j]==reference::batch_word_ref(queries[lo+j],tree,j)) != cfg!(NDI_invert_key_step))]
fn key_iteration(queries:&[u32;22],lo:usize,n:usize,tree:usize,j:usize,keys:&mut[u64;16]) {
        let u = queries[lo + j];
        let index = if tree == 2 { u / 4 } else { u };
        keys[j] = (u64::from(index) << 8) | j as u64;
}
#[kani::proof_for_contract(key_iteration)] #[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn key_contract(){let queries:[u32;22]=kani::any();let mut keys:[u64;16]=kani::any();let batch:bool=kani::any();let (lo,n)=if batch{(10,12)}else{(0,10)};let tree:usize=kani::any();let j:usize=kani::any();kani::assume(tree<3 && j<n);key_iteration(&queries,lo,n,tree,j,&mut keys);}
#[kani::requires(coordinate<16)]
#[kani::ensures(|r| (r[coordinate]==0) != cfg!(NDI_invert_key_init))]
fn key_initial(coordinate:usize)->[u64;16] {
    let mut keys = [0u64; multiproof::MAX_BATCH];
    keys
}
#[kani::proof_for_contract(key_initial)] #[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn key_initial_contract(){let j:usize=kani::any();kani::assume(j<16);let _=key_initial(j);}
#[kani::requires(start<=end && end<=16)]
#[kani::ensures(|r| (*r==reference::range_ref(start,end)) != cfg!(NDI_invert_range))]
fn range_packet(start:usize,end:usize)->(bool,usize,usize,usize){let mut iter=start..end;let reply=iter.next();(reply.is_some(),reply.unwrap_or(0),iter.start,iter.end)}
#[kani::proof_for_contract(range_packet)]
fn range_contract(){let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=end && end<=16);let _=range_packet(start,end);}
#[kani::ensures(|r| r.len()==16)] fn keys_weak()->[u64;16] {[0;16]}
#[kani::proof_for_contract(keys_weak)] #[kani::unwind(18)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn keys_weak_contract(){let _=keys_weak();}
#[kani::proof] #[kani::unwind(18)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn keys_real(){let j:usize=kani::any();kani::assume(j<16);assert_eq!(keys_weak()[j],0);}
#[kani::proof] #[kani::stub_verified(keys_weak)] #[kani::unwind(18)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn keys_unimplied(){let j:usize=kani::any();kani::assume(j<16);assert_eq!(keys_weak()[j],0);}
#[kani::modifies(&mut x[0])] fn keys_badframe(x:&mut[u64;2])->[u64;16] {x[1]=x[1].wrapping_add(1);[0;16]}
#[kani::proof_for_contract(keys_badframe)] #[kani::unwind(18)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn keys_frame(){let mut x:[u64;2]=kani::any();let _=keys_badframe(&mut x);}

#[kani::ensures(|r| (*r==reference::tail_predicate_ref(x)) != cfg!(NDI_invert_tail))]
fn tail_predicate(x:u8)->bool {x!=0}
#[kani::proof_for_contract(tail_predicate)]
fn tail_predicate_contract(){let x:u8=kani::any();let _=tail_predicate(x);}
#[kani::ensures(|r| (*r==reference::contains_predicate_ref(x,q)) != cfg!(NDI_invert_contains))]
fn contains_predicate(x:u32,q:u32)->bool {[x].contains(&q)}
#[kani::proof_for_contract(contains_predicate)] #[kani::unwind(3)]
fn contains_predicate_contract(){let x:u32=kani::any();let q:u32=kani::any();let _=contains_predicate(x,q);}
#[kani::requires(start<=22 && count<=22-start)]
#[kani::ensures(|r| (*r==reference::iter_meta_ref(count)) != cfg!(NDI_invert_iter))]
fn iter_metadata(bytes:&[u8;22],start:usize,count:usize)->(bool,bool,usize) {
 let slice=&bytes[start..start+count];let mut iter=slice.iter();let out=iter.next();
 let pointer=if count>0{core::ptr::eq(out.unwrap(),slice.as_ptr()) && iter.as_slice().as_ptr()==unsafe{slice.as_ptr().add(1)}}else{out.is_none() && iter.as_slice().as_ptr()==slice.as_ptr()};
 (out.is_some(),pointer,iter.as_slice().len())
}
#[kani::proof_for_contract(iter_metadata)]
fn iter_metadata_contract(){let bytes:[u8;22]=kani::any();let start:usize=kani::any();let count:usize=kani::any();kani::assume(start<=22 && count<=22-start);let _=iter_metadata(&bytes,start,count);}
