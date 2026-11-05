//! Ruling (ak): explicit constructors; local records; empty external modifies.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct MetaLog { count:u8,owner:*const Pubkey, expected:*const Pubkey, signer:bool,writable:bool,executable:bool,reply:bool }
fn empty()->MetaLog{MetaLog{count:0,owner:core::ptr::null(),expected:core::ptr::null(),signer:false,writable:false,executable:false,reply:false}}
fn meta_oracle(a:&Pubkey,b:&Pubkey,s:bool,w:bool,e:bool,l:&mut MetaLog)->ProgramResult {
 l.count+=1;l.owner=a;l.expected=b;l.signer=s;l.writable=w;l.executable=e;l.reply=kani::any();
 if l.reply{Ok(())}else{Err(ProgramError::InvalidAccountData)}
}
fn readonly_cut(account:&OwnedAccount,owner:&Pubkey,l:&mut MetaLog)->ProgramResult {
 meta_oracle(account.owner(),owner,account.is_signer,account.is_writable,account.executable,l)
}
fn account()->core::mem::ManuallyDrop<OwnedAccount>{core::mem::ManuallyDrop::new(OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Err(ProgramError::AccountBorrowFailed),bytes:Err(ProgramError::AccountBorrowFailed)})}
fn association(a:&OwnedAccount,k:&Pubkey,l:&MetaLog,r:&ProgramResult)->bool{
 l.count==1&&l.owner==&a.owner as *const Pubkey&&l.expected==k as *const Pubkey&&l.signer==a.is_signer&&l.writable==a.is_writable&&l.executable==a.executable&&if l.reply{r.is_ok()}else{matches!(r,Err(ProgramError::InvalidAccountData))}
}
#[kani::requires(l.count==0)]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn readonly_packet(a:&OwnedAccount,k:&Pubkey,l:&mut MetaLog)->bool{let r=readonly_cut(a,k,l);association(a,k,l,&r)}
#[kani::proof_for_contract(readonly_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_logging(){let a=account();let k=Pubkey::new_from_array(kani::any());let mut l=empty();let _=readonly_packet(&a,&k,&mut l);}
#[kani::requires(l.count==0)]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn readonly_corrupt_packet(a:&OwnedAccount,k:&Pubkey,l:&mut MetaLog)->bool{let r=readonly_cut(a,k,l);l.signer=!l.signer;association(a,k,l,&r)}
#[kani::proof_for_contract(readonly_corrupt_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_logging_corrupt(){let a=account();let k=Pubkey::new_from_array(kani::any());let mut l=empty();let _=readonly_corrupt_packet(&a,&k,&mut l);}

struct ErrorLog { count:u8,input:*const ProgramError,reply:bool }
fn error_empty()->ErrorLog{ErrorLog{count:0,input:core::ptr::null(),reply:false}}
fn error_oracle(e:&ProgramError,l:&mut ErrorLog)->ProgramError{
 assert!(matches!(e,ProgramError::AccountBorrowFailed|ProgramError::InvalidAccountData));
 l.count+=1;l.input=e;l.reply=kani::any();
 if l.reply{ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData}
}
fn data_cut<'a>(a:&'a OwnedAccount,l:&mut ErrorLog)->Result<&'a[u8],ProgramError>{
 match &a.bytes {Ok(bytes)=>Ok(bytes),Err(error)=>Err(error_oracle(error,l))}
}
fn data_association(a:&OwnedAccount,l:&ErrorLog,r:&Result<&[u8],ProgramError>)->bool{
 match &a.bytes {
  Ok(v)=>l.count==0&&match r{Ok(s)=>s.as_ptr()==v.as_ptr()&&s.len()==v.len(),_=>false},
  Err(e)=>l.count==1&&l.input==e as *const ProgramError&&if l.reply{matches!(r,Err(ProgramError::AccountBorrowFailed))}else{matches!(r,Err(ProgramError::InvalidAccountData))}
 }
}
#[kani::requires(l.count==0 && matches!(&a.bytes,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData)))]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn data_packet(a:&OwnedAccount,l:&mut ErrorLog)->bool{let r=data_cut(a,l);data_association(a,l,&r)}
#[kani::proof_for_contract(data_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_logging(){let mut a=account();let shape:u8=kani::any();kani::assume(shape<3);if shape==0{let n:usize=kani::any();kani::assume(n<=4);let mut v=kani::vec::exact_vec::<u8,4>();v.truncate(n);a.bytes=Ok(v);}else if shape==2{a.bytes=Err(ProgramError::InvalidAccountData);}let mut l=error_empty();let _=data_packet(&a,&mut l);}
#[kani::requires(l.count==0 && matches!(&a.bytes,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData)))]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn data_corrupt_packet(a:&OwnedAccount,l:&mut ErrorLog)->bool{let r=data_cut(a,l);if l.count==1{l.reply=!l.reply;}data_association(a,l,&r)}
#[kani::proof_for_contract(data_corrupt_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_logging_corrupt(){let a=account();let mut l=error_empty();let _=data_corrupt_packet(&a,&mut l);}

// Exact pinned core Result::clone match, with only Err payload clone cut.
fn length_clone_cut(r:&Result<usize,ProgramError>,l:&mut ErrorLog)->Result<usize,ProgramError>{
 match r {Ok(x)=>Ok(x.clone()),Err(x)=>Err(error_oracle(x,l))}
}
fn length_cut(a:&OwnedAccount,l:&mut ErrorLog)->Result<usize,ProgramError>{length_clone_cut(&a.length,l)}
fn length_association(a:&OwnedAccount,l:&ErrorLog,r:&Result<usize,ProgramError>)->bool{
 match &a.length {
  Ok(n)=>l.count==0&&matches!(r,Ok(m) if m==n),
  Err(e)=>l.count==1&&l.input==e as *const ProgramError&&if l.reply{matches!(r,Err(ProgramError::AccountBorrowFailed))}else{matches!(r,Err(ProgramError::InvalidAccountData))}
 }
}
#[kani::requires(l.count==0 && matches!(&a.length,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData)))]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn length_packet(a:&OwnedAccount,l:&mut ErrorLog)->bool{let r=length_cut(a,l);length_association(a,l,&r)}
#[kani::proof_for_contract(length_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_logging(){let mut a=account();let shape:u8=kani::any();kani::assume(shape<3);a.length=if shape==0{Ok(kani::any())}else if shape==1{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)};let mut l=error_empty();let _=length_packet(&a,&mut l);}
#[kani::requires(l.count==0 && matches!(&a.length,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData)))]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn length_corrupt_packet(a:&OwnedAccount,l:&mut ErrorLog)->bool{let r=length_cut(a,l);l.count=l.count.wrapping_add(1);length_association(a,l,&r)}
#[kani::proof_for_contract(length_corrupt_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_logging_corrupt(){let mut a=account();let shape:bool=kani::any();a.length=if shape{Ok(kani::any())}else{Err(ProgramError::AccountBorrowFailed)};let mut l=error_empty();let _=length_corrupt_packet(&a,&mut l);}
