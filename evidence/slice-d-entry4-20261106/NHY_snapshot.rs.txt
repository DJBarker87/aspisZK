//! Both SDK Result constructors, local borrow log. Original guard is moved/dropped.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct BorrowLog {count:u8,receiver:*const (),ok:bool}
fn oracle<'a,'b>(account:&'a AccountInfo<'b>, log:&mut BorrowLog)->Result<core::cell::Ref<'a,&'b mut [u8]>,ProgramError>{
 log.count+=1;log.receiver=account as *const _ as *const ();log.ok=kani::any();
 if log.ok {Ok(account.data.borrow())} else {Err(ProgramError::AccountBorrowFailed)}
}
fn cut(account:&AccountInfo<'_>,length1:usize,length2:usize,log:&mut BorrowLog)->OwnedAccount {
 let (length,bytes)=match oracle(account,log) {
  Ok(data)=>{let length=data.len();let bytes=if length==length1||length==length2 {Ok(data.to_vec())}else{Err(ProgramError::InvalidAccountData)};(Ok(length),bytes)}
  Err(error)=>(Err(error.clone()),Err(error)),
 };
 OwnedAccount{key:*account.key,owner:*account.owner,is_signer:account.is_signer,is_writable:account.is_writable,executable:account.executable,length,bytes}
}
fn matches(r:&OwnedAccount,a:&AccountInfo<'_>,l1:usize,l2:usize,l:&BorrowLog,original:u8)->bool{
 l.count==1&&l.receiver==a as *const _ as *const ()&&r.key==*a.key&&r.owner==*a.owner&&r.is_signer==a.is_signer&&r.is_writable==a.is_writable&&r.executable==a.executable&&
 if l.ok {matches!(r.length,Ok(1))&&if l1==1||l2==1 {match &r.bytes{Ok(v)=>v.len()==1&&v[0]==original,Err(_)=>false}}else{matches!(r.bytes,Err(ProgramError::InvalidAccountData))}}
 else{matches!(r.length,Err(ProgramError::AccountBorrowFailed))&&matches!(r.bytes,Err(ProgramError::AccountBorrowFailed))}
}
#[kani::requires(log.count==0)]
#[kani::requires(a.data.borrow().len()==1)]
#[kani::ensures(|r|*r)] #[kani::modifies(log)]
fn packet(a:&AccountInfo<'_>,l1:usize,l2:usize,log:&mut BorrowLog)->bool{
 let original=a.data.borrow()[0];let r=cut(a,l1,l2,log);matches(&r,a,l1,l2,log,original)&&a.data.borrow()[0]==original
}
#[kani::requires(log.count==0)]
#[kani::requires(a.data.borrow().len()==1)]
#[kani::ensures(|r|*r)] #[kani::modifies(log)]
fn packet_wrong(a:&AccountInfo<'_>,l1:usize,l2:usize,log:&mut BorrowLog)->bool{
 let original=a.data.borrow()[0];let r=cut(a,l1,l2,log);log.ok=!log.ok;matches(&r,a,l1,l2,log,original)&&a.data.borrow()[0]==original
}
macro_rules! harness {($name:ident,$f:ident)=>{
 #[kani::proof_for_contract($f)] #[kani::unwind(35)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 fn $name(){let k=Pubkey::new_from_array(kani::any());let o=Pubkey::new_from_array(kani::any());let mut lamports=kani::any();let mut data=[kani::any()];let a=AccountInfo::new(&k,kani::any(),kani::any(),&mut lamports,&mut data,&o,kani::any(),kani::any());let mut log=BorrowLog{count:0,receiver:core::ptr::null(),ok:false};$f(&a,kani::any(),kani::any(),&mut log);}
}}
harness!(both_arms,packet);
harness!(both_arms_wrong,packet_wrong);

// Split at the SDK guard dereference and before allocation: Ref/SDK lifetime is
// the retained NHJ bracket packet, not a manufactured guard or copy oracle.
struct HeaderLog {count:u8,receiver:*const (),bytes:*const u8,length:usize,ok:bool}
fn borrowed_oracle<'a>(account:&AccountInfo<'_>,bytes:&'a [u8],log:&mut HeaderLog)->Result<&'a [u8],ProgramError>{
 log.count+=1;log.receiver=account as *const _ as *const ();log.bytes=bytes.as_ptr();log.length=bytes.len();log.ok=kani::any();
 if log.ok{Ok(bytes)}else{Err(ProgramError::AccountBorrowFailed)}
}
enum Head {Copy{length:usize},Done(OwnedAccount)}
fn header(a:&AccountInfo<'_>,bytes:&[u8],l1:usize,l2:usize,log:&mut HeaderLog)->Head{
 let (length,bytes)=match borrowed_oracle(a,bytes,log){
  Ok(data)=>{let length=data.len();if length==l1||length==l2{return Head::Copy{length};}(Ok(length),Err(ProgramError::InvalidAccountData))}
  Err(error)=>(Err(error.clone()),Err(error)),
 };
 Head::Done(OwnedAccount{key:*a.key,owner:*a.owner,is_signer:a.is_signer,is_writable:a.is_writable,executable:a.executable,length,bytes})
}
fn header_matches(r:&Head,a:&AccountInfo<'_>,bytes:&[u8],l1:usize,l2:usize,log:&HeaderLog)->bool{
 if log.count!=1||log.receiver!=a as *const _ as *const ()||log.bytes!=bytes.as_ptr()||log.length!=bytes.len(){return false;}
 match r{Head::Copy{length}=>log.ok&&*length==bytes.len()&&(*length==l1||*length==l2),Head::Done(r)=>
 r.key==*a.key&&r.owner==*a.owner&&r.is_signer==a.is_signer&&r.is_writable==a.is_writable&&r.executable==a.executable&&
 if log.ok{bytes.len()!=l1&&bytes.len()!=l2&&matches!(r.length,Ok(n)if n==bytes.len())&&matches!(r.bytes,Err(ProgramError::InvalidAccountData))}
 else{matches!(r.length,Err(ProgramError::AccountBorrowFailed))&&matches!(r.bytes,Err(ProgramError::AccountBorrowFailed))}}
}
#[kani::requires(log.count==0)] #[kani::ensures(|r|*r)] #[kani::modifies(log)]
fn header_packet(a:&AccountInfo<'_>,bytes:&[u8],l1:usize,l2:usize,log:&mut HeaderLog)->bool{let r=header(a,bytes,l1,l2,log);header_matches(&r,a,bytes,l1,l2,log)}
#[kani::requires(log.count==0)] #[kani::ensures(|r|*r)] #[kani::modifies(log)]
fn header_wrong_packet(a:&AccountInfo<'_>,bytes:&[u8],l1:usize,l2:usize,log:&mut HeaderLog)->bool{let r=header(a,bytes,l1,l2,log);log.ok=!log.ok;header_matches(&r,a,bytes,l1,l2,log)}
macro_rules! head_harness {($name:ident,$f:ident)=>{
 #[kani::proof_for_contract($f)] #[kani::unwind(35)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 fn $name(){let k=Pubkey::new_from_array(kani::any());let o=Pubkey::new_from_array(kani::any());let mut lamports=kani::any();let mut data=[kani::any()];let a=AccountInfo::new(&k,kani::any(),kani::any(),&mut lamports,&mut data,&o,kani::any(),kani::any());let bytes=[kani::any();1];let mut log=HeaderLog{count:0,receiver:core::ptr::null(),bytes:core::ptr::null(),length:0,ok:false};$f(&a,&bytes,kani::any(),kani::any(),&mut log);}
}}
head_harness!(both_header_arms,header_packet);
head_harness!(both_header_arms_wrong,header_wrong_packet);

// Further split: the canonical ProgramError clone is an already CLOSED child.
struct CloneLog {count:u8,expected:*const ProgramError,receiver:*const ProgramError,reply:bool}
fn clone_oracle(e:&ProgramError,l:&mut CloneLog)->ProgramError{l.count+=1;l.receiver=e;l.reply=kani::any();if l.reply{ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData}}
fn header_clone_cut(a:&AccountInfo<'_>,bytes:&[u8],l1:usize,l2:usize,log:&mut HeaderLog,clone:&mut CloneLog)->Head{
 let (length,bytes)=match borrowed_oracle(a,bytes,log){
  Ok(data)=>{let length=data.len();if length==l1||length==l2{return Head::Copy{length};}(Ok(length),Err(ProgramError::InvalidAccountData))}
  Err(error)=>{clone.expected=&error;let result=clone_oracle(&error,clone);(Err(result),Err(error))},
 };
 Head::Done(OwnedAccount{key:*a.key,owner:*a.owner,is_signer:a.is_signer,is_writable:a.is_writable,executable:a.executable,length,bytes})
}
fn light_matches(r:&Head,a:&AccountInfo<'_>,bytes:&[u8],l1:usize,l2:usize,log:&HeaderLog,clone:&CloneLog)->bool{
 if log.ok{return clone.count==0&&header_matches(r,a,bytes,l1,l2,log);}
 if log.count!=1||log.receiver!=a as *const _ as *const ()||log.bytes!=bytes.as_ptr()||log.length!=bytes.len()||clone.count!=1||clone.receiver!=clone.expected{return false;}
 match r{Head::Copy{..}=>false,Head::Done(r)=>r.key==*a.key&&r.owner==*a.owner&&r.is_signer==a.is_signer&&r.is_writable==a.is_writable&&r.executable==a.executable&&matches!(r.bytes,Err(ProgramError::AccountBorrowFailed))&&if clone.reply{matches!(r.length,Err(ProgramError::AccountBorrowFailed))}else{matches!(r.length,Err(ProgramError::InvalidAccountData))}}
}
#[kani::requires(log.count==0&&clone.count==0)] #[kani::ensures(|r|*r)] #[kani::modifies(log,clone)]
fn light_packet(a:&AccountInfo<'_>,bytes:&[u8],l1:usize,l2:usize,log:&mut HeaderLog,clone:&mut CloneLog)->bool{let r=core::mem::ManuallyDrop::new(header_clone_cut(a,bytes,l1,l2,log,clone));light_matches(&r,a,bytes,l1,l2,log,clone)}
#[kani::requires(log.count==0&&clone.count==0)] #[kani::ensures(|r|*r)] #[kani::modifies(log,clone)]
fn light_wrong_packet(a:&AccountInfo<'_>,bytes:&[u8],l1:usize,l2:usize,log:&mut HeaderLog,clone:&mut CloneLog)->bool{let r=core::mem::ManuallyDrop::new(header_clone_cut(a,bytes,l1,l2,log,clone));log.count=0;light_matches(&r,a,bytes,l1,l2,log,clone)}
macro_rules! light_harness {($name:ident,$f:ident)=>{
 #[kani::proof_for_contract($f)] #[kani::unwind(35)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 fn $name(){let k=Pubkey::new_from_array(kani::any());let o=Pubkey::new_from_array(kani::any());let mut lamports=kani::any();let mut data=[kani::any()];let a=core::mem::ManuallyDrop::new(AccountInfo::new(&k,kani::any(),kani::any(),&mut lamports,&mut data,&o,kani::any(),kani::any()));let bytes=[kani::any();1];let mut log=HeaderLog{count:0,receiver:core::ptr::null(),bytes:core::ptr::null(),length:0,ok:false};let mut clone=CloneLog{count:0,expected:core::ptr::null(),receiver:core::ptr::null(),reply:false};$f(&a,&bytes,kani::any(),kani::any(),&mut log,&mut clone);}
}}
light_harness!(borrow_clone_header,light_packet);
light_harness!(borrow_clone_header_wrong,light_wrong_packet);
// Full descriptor domain. SDK reply payload is a scalar length projection;
// no invented large slice and no length restriction. Source bytes are not read.
fn dispatch(ok:bool,length:usize,l1:usize,l2:usize)->u8{
 if ok{if length==l1||length==l2{0}else{1}}else{2}
}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn dispatch_packet(ok:bool,length:usize,l1:usize,l2:usize)->bool{
 let r=dispatch(ok,length,l1,l2);
 if !ok{r==2}else if (length as u128)==(l1 as u128)||(length as u128)==(l2 as u128){r==0}else{r==1}
}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn dispatch_wrong_packet(ok:bool,length:usize,l1:usize,l2:usize)->bool{
 let r=dispatch(ok,length,l1,l2)^4;
 if !ok{r==2}else if (length as u128)==(l1 as u128)||(length as u128)==(l2 as u128){r==0}else{r==1}
}
#[kani::proof_for_contract(dispatch_packet)] fn descriptor_dispatch(){dispatch_packet(kani::any(),kani::any(),kani::any(),kani::any());}
#[kani::proof_for_contract(dispatch_wrong_packet)] fn descriptor_dispatch_wrong(){dispatch_wrong_packet(kani::any(),kani::any(),kani::any(),kani::any());}
