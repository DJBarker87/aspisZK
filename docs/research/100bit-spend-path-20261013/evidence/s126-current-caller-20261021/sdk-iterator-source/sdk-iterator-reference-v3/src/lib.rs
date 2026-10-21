#![allow(dead_code,unexpected_cfgs)]
use aspis_s126_owned_sdk::OwnedSdk;
#[derive(Clone,Copy)]
pub struct DataPointer {pub slot:usize,pub offset:usize}
#[derive(Clone,Copy)]
pub struct SourceIterator {pub ptr:DataPointer,pub end_or_len:DataPointer}
pub fn source_begin(sdk:&OwnedSdk,slot:usize)->SourceIterator {
 SourceIterator {ptr:DataPointer{slot,offset:0},end_or_len:DataPointer{slot,offset:sdk.data_cells[slot].bytes.len()}}
}
pub fn source_next(sdk:&OwnedSdk,iter:&mut SourceIterator)->Option<u8> {
 assert!(iter.ptr.slot==iter.end_or_len.slot);
 assert!(iter.ptr.offset<=iter.end_or_len.offset);
 assert!(iter.end_or_len.offset<=sdk.data_cells[iter.ptr.slot].bytes.len());
 if iter.ptr.offset==iter.end_or_len.offset {return None;}
 let byte=sdk.data_cells[iter.ptr.slot].bytes[iter.ptr.offset];
 iter.ptr.offset+=1;
 Some(byte)
}
#[cfg(kani)] mod proofs {
use super::*;
use aspis_s126_owned_sdk::{OwnedAccount,OwnedDataCell,OwnedLamportsCell};
use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
#[kani::proof] #[kani::unwind(36)]
fn actual_sdk_next_reference_join() {
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let flags:[bool;3]=kani::any();let rent_epoch:u64=kani::any();
 let mut lamports:u64=kani::any();let initial_lamports=lamports;
 let mut bytes:[u8;1768]=kani::any();let snapshot=bytes.to_vec();
 let cursor:usize=kani::any();kani::assume(cursor<=1768);
 let account=AccountInfo::new(&key,flags[0],flags[1],&mut lamports,&mut bytes,&owner,flags[2],rent_epoch);
 let model=OwnedSdk{
  accounts:vec![OwnedAccount{key:key.to_bytes(),owner:owner.to_bytes(),is_signer:flags[0],is_writable:flags[1],executable:flags[2],rent_epoch,data_slot:0,lamports_slot:0}],
  data_cells:vec![OwnedDataCell{bytes:snapshot,borrowed:-1,strong:std::rc::Rc::strong_count(&account.data),weak:std::rc::Rc::weak_count(&account.data)}],
  lamports_cells:vec![OwnedLamportsCell{amount:initial_lamports,borrowed:0,strong:std::rc::Rc::strong_count(&account.lamports),weak:std::rc::Rc::weak_count(&account.lamports)}],
 };
 let data=account.try_borrow_mut_data().unwrap();
 let mut iter=data[cursor..].iter();let base=data.as_ptr();
 let mut expected=source_begin(&model,0);
 let whole=data.iter();
 assert_eq!(whole.as_slice().as_ptr(),unsafe{base.add(expected.ptr.offset)});
 assert_eq!(whole.len(),expected.end_or_len.offset-expected.ptr.offset);
 assert_eq!(expected.ptr.slot,0);assert_eq!(expected.end_or_len.slot,0);
 assert_eq!(expected.ptr.offset,0);assert_eq!(expected.end_or_len.offset,1768);
 expected.ptr.offset=cursor;
 let outcome=iter.next().copied();let reference=source_next(&model,&mut expected);
 assert_eq!(outcome,reference);
 assert_eq!(iter.as_slice().as_ptr(),unsafe{base.add(expected.ptr.offset)});
 assert_eq!(iter.len(),expected.end_or_len.offset-expected.ptr.offset);
 assert_eq!(expected.ptr.slot,0);assert_eq!(expected.end_or_len.slot,0);
 assert_eq!(expected.end_or_len.offset,1768);
 // SDK next may update the iterator but must leave the live heap untouched.
 assert_eq!(model.data_cells[0].borrowed,-1);
 assert_eq!(**account.try_borrow_lamports().unwrap(),model.lamports_cells[0].amount);
 kani::cover!(cursor==1768,"empty native next matches owned source");
 kani::cover!(outcome==Some(0),"zero native byte matches owned source");
 kani::cover!(outcome.is_some()&&outcome!=Some(0),"nonzero native byte matches owned source");
}
}
