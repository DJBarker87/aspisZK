use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use core::cell::{Ref,RefMut};
use std::rc::Rc;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// Observation only: never fabricate a guard or change a borrow flag.
fn data_counter(a:&AccountInfo)->isize{unsafe{*Rc::as_ptr(&a.data).cast::<isize>()}}
fn lamports_counter(a:&AccountInfo)->isize{unsafe{*Rc::as_ptr(&a.lamports).cast::<isize>()}}
macro_rules! setup {($body:expr)=>{{
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut money:u64=kani::any();let mut bytes:[u8;2]=kani::any();let p=bytes.as_ptr();let value=bytes[0];let m=money;
 let a=AccountInfo::new(&key,false,true,&mut money,&mut bytes,&owner,false,0);
 assert!(core::ptr::eq(a.key,&key));assert!(core::ptr::eq(a.owner,&owner));
 assert_eq!(data_counter(&a),0);assert_eq!(lamports_counter(&a),0);
 ($body)(&a,p,value,m);
 assert!(core::ptr::eq(a.key,&key));assert!(core::ptr::eq(a.owner,&owner));
 assert_eq!(data_counter(&a),0);assert_eq!(lamports_counter(&a),0);
}}}
#[kani::proof] #[kani::unwind(129)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn shared_free(){setup!(|a:&AccountInfo,p,value,_|{
 let r=a.try_borrow_data();assert!(r.is_ok());let g=r.unwrap();
 assert_eq!(data_counter(a),1);assert_eq!(lamports_counter(a),0);
 assert_eq!(g.as_ptr(),p);assert_eq!(g.len(),2);assert_eq!(g[0],value);
 let moved=g;assert_eq!(moved.as_ptr(),p);drop(moved);assert_eq!(data_counter(a),0);
});}
#[kani::proof] #[kani::unwind(129)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn shared_wrong_cell(){setup!(|a:&AccountInfo,_,_,_|{
 let g=a.try_borrow_data().unwrap();assert_eq!(lamports_counter(a),1);drop(g);
});}
#[kani::proof] #[kani::unwind(129)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn exclusive_free(){setup!(|a:&AccountInfo,p,value,_|{
 let mut g=a.try_borrow_mut_data().unwrap();assert_eq!(data_counter(a),-1);assert_eq!(lamports_counter(a),0);
 assert_eq!(g.as_ptr(),p);assert_eq!(g.len(),2);assert_eq!(g[0],value);
 let x:u8=kani::any();g[0]=x;assert_eq!(g[0],x);let moved=g;drop(moved);assert_eq!(data_counter(a),0);
});}
#[kani::proof] #[kani::unwind(129)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn exclusive_wrong_counter(){setup!(|a:&AccountInfo,_,_,_|{
 let g=a.try_borrow_mut_data().unwrap();assert_eq!(data_counter(a),1);drop(g);
});}
macro_rules! proof {($name:ident,$body:expr)=>{
 #[kani::proof] #[kani::unwind(129)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 fn $name(){setup!($body);}
}}
proof!(shared_conflict,|a:&AccountInfo,_,_,_|{let held=a.try_borrow_mut_data().unwrap();let r=a.try_borrow_data();assert!(matches!(r,Err(ProgramError::AccountBorrowFailed)));assert_eq!(data_counter(a),-1);drop(r);drop(held);});
proof!(shared_conflict_control,|a:&AccountInfo,_,_,_|{let held=a.try_borrow_mut_data().unwrap();let r=a.try_borrow_data();assert!(r.is_ok());drop(r);drop(held);});
proof!(exclusive_shared_conflict,|a:&AccountInfo,_,_,_|{let held=a.try_borrow_data().unwrap();let r=a.try_borrow_mut_data();assert!(matches!(r,Err(ProgramError::AccountBorrowFailed)));assert_eq!(data_counter(a),1);drop(r);drop(held);});
proof!(exclusive_shared_control,|a:&AccountInfo,_,_,_|{let held=a.try_borrow_data().unwrap();let r=a.try_borrow_mut_data();assert!(r.is_ok());drop(r);drop(held);});
proof!(exclusive_exclusive_conflict,|a:&AccountInfo,_,_,_|{let held=a.try_borrow_mut_data().unwrap();let r=a.try_borrow_mut_data();assert!(matches!(r,Err(ProgramError::AccountBorrowFailed)));assert_eq!(data_counter(a),-1);drop(r);drop(held);});
proof!(exclusive_exclusive_control,|a:&AccountInfo,_,_,_|{let held=a.try_borrow_mut_data().unwrap();let r=a.try_borrow_mut_data();assert!(r.is_ok());drop(r);drop(held);});
proof!(lamports_shared,|a:&AccountInfo,_,_,m|{let g=a.try_borrow_lamports().unwrap();assert_eq!(lamports_counter(a),1);assert_eq!(data_counter(a),0);assert_eq!(**g,m);drop(g);});
proof!(lamports_shared_control,|a:&AccountInfo,_,_,_|{let g=a.try_borrow_lamports().unwrap();assert_eq!(data_counter(a),1);drop(g);});
proof!(lamports_exclusive,|a:&AccountInfo,_,_,m|{let mut g=a.try_borrow_mut_lamports().unwrap();assert_eq!(lamports_counter(a),-1);assert_eq!(data_counter(a),0);assert_eq!(**g,m);let v:u64=kani::any();**g=v;drop(g);assert_eq!(a.lamports(),v);});
proof!(lamports_exclusive_control,|a:&AccountInfo,_,_,_|{let g=a.try_borrow_mut_lamports().unwrap();assert_eq!(lamports_counter(a),1);drop(g);});
proof!(data_len_getters,|a:&AccountInfo,_,_,_|{let g=a.try_borrow_data().unwrap();assert_eq!(a.data_len(),2);assert_eq!(a.try_data_len(),Ok(2));assert_eq!(data_counter(a),1);drop(g);});
proof!(data_len_control,|a:&AccountInfo,_,_,_|{assert_eq!(a.try_data_len(),Ok(3));});
proof!(metadata_getters,|a:&AccountInfo,_,_,m|{assert_eq!(a.lamports(),m);assert_eq!(a.try_lamports(),Ok(m));assert!(core::ptr::eq(a.unsigned_key(),a.key));assert!(core::ptr::eq(a.owner,a.owner));assert_eq!(data_counter(a),0);assert_eq!(lamports_counter(a),0);});
proof!(metadata_control,|a:&AccountInfo,_,_,m:u64|{assert_eq!(a.try_lamports(),Ok(m.wrapping_add(1)));});
proof!(shared_map,|a:&AccountInfo,p,v,_|{let g=a.try_borrow_data().unwrap();let m=Ref::map(g,|s|&s[0]);assert_eq!(data_counter(a),1);assert_eq!(*m,v);assert_eq!((&*m) as *const u8,p);drop(m);});
proof!(shared_map_control,|a:&AccountInfo,_,_,_|{let g=a.try_borrow_data().unwrap();let m=Ref::map(g,|s|&s[0]);assert_eq!(data_counter(a),2);drop(m);});
proof!(exclusive_map,|a:&AccountInfo,p,v,_|{let g=a.try_borrow_mut_data().unwrap();let mut m=RefMut::map(g,|s|&mut s[0]);assert_eq!(data_counter(a),-1);assert_eq!(*m,v);assert_eq!((&*m) as *const u8,p);let x:u8=kani::any();*m=x;assert_eq!(*m,x);drop(m);});
proof!(exclusive_map_control,|a:&AccountInfo,_,_,_|{let g=a.try_borrow_mut_data().unwrap();let m=RefMut::map(g,|s|&mut s[0]);assert_eq!(data_counter(a),0);drop(m);});
proof!(error_drop,|a:&AccountInfo,_,_,_|{let g=a.try_borrow_mut_data().unwrap();let r=a.try_borrow_data();assert!(matches!(r,Err(ProgramError::AccountBorrowFailed)));drop(r);assert_eq!(data_counter(a),-1);drop(g);});
proof!(error_drop_control,|a:&AccountInfo,_,_,_|{let g=a.try_borrow_mut_data().unwrap();let r=a.try_borrow_data();drop(r);assert_eq!(data_counter(a),0);drop(g);});
proof!(shared_seven,|a:&AccountInfo,_,_,_|{let g0=a.try_borrow_data().unwrap();let g1=a.try_borrow_data().unwrap();let g2=a.try_borrow_data().unwrap();let g3=a.try_borrow_data().unwrap();let g4=a.try_borrow_data().unwrap();let g5=a.try_borrow_data().unwrap();let g6=a.try_borrow_data().unwrap();assert_eq!(data_counter(a),7);assert!(matches!(a.try_borrow_mut_data(),Err(ProgramError::AccountBorrowFailed)));drop(g3);drop(g0);drop(g6);assert_eq!(data_counter(a),4);drop(g1);drop(g5);drop(g4);drop(g2);});
proof!(shared_seven_control,|a:&AccountInfo,_,_,_|{let g0=a.try_borrow_data().unwrap();let g1=a.try_borrow_data().unwrap();let g2=a.try_borrow_data().unwrap();let g3=a.try_borrow_data().unwrap();let g4=a.try_borrow_data().unwrap();let g5=a.try_borrow_data().unwrap();let g6=a.try_borrow_data().unwrap();drop(g3);assert_eq!(data_counter(a),7);drop((g0,g1,g2,g4,g5,g6));});
proof!(lamports_conflict,|a:&AccountInfo,_,_,_|{let g=a.try_borrow_mut_lamports().unwrap();assert!(matches!(a.try_borrow_lamports(),Err(ProgramError::AccountBorrowFailed)));assert!(matches!(a.try_borrow_mut_lamports(),Err(ProgramError::AccountBorrowFailed)));assert_eq!(a.try_lamports(),Err(ProgramError::AccountBorrowFailed));assert_eq!(lamports_counter(a),-1);drop(g);});
proof!(lamports_conflict_control,|a:&AccountInfo,_,_,_|{let g=a.try_borrow_mut_lamports().unwrap();assert!(a.try_lamports().is_ok());drop(g);});
proof!(empty_getters,|a:&AccountInfo,_,_,_|{assert!(!a.data_is_empty());assert_eq!(a.try_data_is_empty(),Ok(false));let g=a.try_borrow_mut_data().unwrap();assert_eq!(a.try_data_is_empty(),Err(ProgramError::AccountBorrowFailed));assert_eq!(a.try_data_len(),Err(ProgramError::AccountBorrowFailed));drop(g);});
proof!(empty_control,|a:&AccountInfo,_,_,_|{assert_eq!(a.try_data_is_empty(),Ok(true));});
#[kani::proof] #[kani::unwind(129)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn group_conflicts(){shared_conflict();exclusive_shared_conflict();exclusive_exclusive_conflict();error_drop();}
#[kani::proof] #[kani::unwind(129)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn group_lamports(){lamports_shared();lamports_exclusive();lamports_conflict();metadata_getters();}
#[kani::proof] #[kani::unwind(129)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn group_scalars(){data_len_getters();metadata_getters();empty_getters();}
#[kani::proof] #[kani::unwind(129)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn group_maps(){shared_map();exclusive_map();}
