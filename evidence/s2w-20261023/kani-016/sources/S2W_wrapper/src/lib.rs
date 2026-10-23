#![cfg(kani)]
#![allow(non_snake_case, dead_code)]
// Selected-cell semantics of the authorized SDK/std primitives. This crate
// checks source control flow under that interpretation, not SDK internals or
// foreign guard layout. The full-heap interpretation is a separate Lean gate.
use std::{cell::{RefCell, Ref, RefMut}, marker::PhantomData};
type Pubkey = [u8;32];
#[derive(Clone,Copy,PartialEq,Eq,Debug)]
enum ProgramError { InvalidAccountData, AccountBorrowFailed }
#[derive(Clone,Copy,PartialEq,Eq,Debug)]
struct Projection { length: usize, index: usize, byte: u8 }
impl Projection {
    fn len(&self)->usize { self.length }
    fn to_vec(&self)->Vec<u8> { Vec(*self,PhantomData) }
    fn copy_from_slice(&mut self, src:&Projection) {
        assert!(self.length == src.length && self.index == src.index);
        self.byte=src.byte;
    }
}
#[derive(Clone,Copy)]
struct Vec<T>(Projection,PhantomData<T>);
impl<T> std::ops::Deref for Vec<T> {
    type Target=Projection;
    fn deref(&self)->&Projection { &self.0 }
}
struct AccountInfo<'a> {
    key:&'a Pubkey, owner:&'a Pubkey, is_signer:bool, is_writable:bool,
    executable:bool, data:RefCell<Projection>, lamports:u64, epoch:u64,
}
impl AccountInfo<'_> {
    fn try_borrow_data(&self)->Result<Ref<'_,Projection>,ProgramError> {
        self.data.try_borrow().map_err(|_|ProgramError::AccountBorrowFailed)
    }
    fn try_borrow_mut_data(&self)->Result<RefMut<'_,Projection>,ProgramError> {
        self.data.try_borrow_mut().map_err(|_|ProgramError::AccountBorrowFailed)
    }
}
// BEGIN VERBATIM NATIVE SNAPSHOT
struct OwnedAccount {
    key: Pubkey,
    owner: Pubkey,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
    length: Result<usize, ProgramError>,
    bytes: Result<Vec<u8>, ProgramError>,
}
// Copy only decoder-admitted lengths; malformed lengths retain their original
// length and a deferred error. No adversarial account length drives allocation.
fn snapshot(account: &AccountInfo<'_>, length1: usize, length2: usize) -> OwnedAccount {
    let (length, bytes) = match account.try_borrow_data() {
        Ok(data) => {
            let length = data.len();
            let bytes = if length == length1 || length == length2 {
                Ok(data.to_vec())
            } else { Err(ProgramError::InvalidAccountData) };
            (Ok(length), bytes)
        }
        Err(error) => (Err(error.clone()), Err(error)),
    };
    OwnedAccount { key: *account.key, owner: *account.owner,
        is_signer: account.is_signer, is_writable: account.is_writable,
        executable: account.executable, length, bytes }
}

// END VERBATIM NATIVE SNAPSHOT
fn S2W_checkpoint_write(accounts:&[AccountInfo<'_>], checkpoint:Vec<u8>) -> Result<(),ProgramError> {
    accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);
    Ok(())
}
fn S2W_account<'a>(key:&'a Pubkey,owner:&'a Pubkey,length:usize,index:usize,byte:u8)->AccountInfo<'a> {
    AccountInfo {key,owner,is_signer:kani::any(),is_writable:kani::any(),
        executable:kani::any(),data:RefCell::new(Projection{length,index,byte}),
        lamports:kani::any(),epoch:kani::any()}
}
fn S2W_snapshot_check(length:usize) {
    let index:usize=kani::any(); kani::assume(index<length);
    let original:u8=kani::any(); let key:Pubkey=kani::any(); let owner:Pubkey=kani::any();
    let account=S2W_account(&key,&owner,length,index,original);
    let metadata=(account.lamports,account.epoch,account.is_signer,account.is_writable,account.executable);
    let result=snapshot(&account,length,length);
    assert!(result.key==key && result.owner==owner);
    assert!(result.is_signer==metadata.2 && result.is_writable==metadata.3 && result.executable==metadata.4);
    assert!(result.length==Ok(length));
    let owned=result.bytes.unwrap();
    assert!(owned.len()==length && owned.index==index && owned.byte==original);
    let mut guard=account.try_borrow_mut_data().unwrap();
    guard.byte=kani::any(); drop(guard);
    assert!(owned.byte==original);
    assert!((account.lamports,account.epoch,account.is_signer,account.is_writable,account.executable)==metadata);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2W_snapshot_proof() { S2W_snapshot_check(57607); }
#[kani::proof]
#[kani::unwind(34)]
fn S2W_snapshot_raw_proof() { S2W_snapshot_check(58295); }
#[kani::proof]
#[kani::unwind(34)]
fn S2W_snapshot_checkpoint() { S2W_snapshot_check(1768); }
#[kani::proof]
#[kani::unwind(34)]
fn S2W_snapshot_public() { S2W_snapshot_check(1880); }
#[kani::proof]
#[kani::unwind(34)]
fn S2W_write_checkpoint() {
    let index:usize=kani::any(); kani::assume(index<1768);
    let key:Pubkey=kani::any(); let owner:Pubkey=kani::any();
    let a=S2W_account(&key,&owner,1768,index,kani::any());
    let b=S2W_account(&key,&owner,1768,index,kani::any());
    let c=S2W_account(&key,&owner,1768,index,kani::any());
    let accounts=[a,b,c];
    let before0=*accounts[0].data.borrow(); let before1=*accounts[1].data.borrow();
    let meta=(accounts[2].lamports,accounts[2].epoch,accounts[2].is_signer,accounts[2].is_writable,accounts[2].executable);
    let src=Projection{length:1768,index,byte:kani::any()};
    assert!(S2W_checkpoint_write(&accounts,Vec(src,PhantomData))==Ok(()));
    assert!(*accounts[2].data.borrow()==src);
    assert!(*accounts[0].data.borrow()==before0 && *accounts[1].data.borrow()==before1);
    assert!((accounts[2].lamports,accounts[2].epoch,accounts[2].is_signer,accounts[2].is_writable,accounts[2].executable)==meta);
    assert!(accounts[2].try_borrow_mut_data().is_ok());
}
#[kani::proof]
#[kani::unwind(34)]
fn S2W_snapshot_deferred_error() {
    let length:usize=kani::any(); let index:usize=kani::any();
    let key:Pubkey=kani::any(); let owner:Pubkey=kani::any();
    let a=S2W_account(&key,&owner,length,index,kani::any());
    kani::assume(length!=1768);
    let s=snapshot(&a,1768,1768);
    assert!(s.length==Ok(length)); assert!(matches!(s.bytes,Err(ProgramError::InvalidAccountData)));
    let guard=a.try_borrow_mut_data().unwrap();
    let failed=snapshot(&a,1768,1768);
    assert!(failed.length==Err(ProgramError::AccountBorrowFailed));
    assert!(matches!(failed.bytes,Err(ProgramError::AccountBorrowFailed)));
    drop(guard); assert!(a.try_borrow_mut_data().is_ok());
}
