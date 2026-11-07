extern crate alloc;
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn none_reply()->Option<(Pubkey,Vec<u8>)>{None}
fn fixed_reply()->Option<(Pubkey,Vec<u8>)>{Some((Pubkey::new_from_array([42;32]),alloc::vec![37]))}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(program::get_return_data,none_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn actual_none(){let mut rt=SolanaPairForestVerifierRuntimeV1;let got=rt.get_return_data();assert!(got.is_none()!=cfg!(PCG_NEG_RETURN));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(program::get_return_data,fixed_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn actual_some(){let mut rt=SolanaPairForestVerifierRuntimeV1;let (key,bytes)=rt.get_return_data().unwrap();assert_eq!(bytes.len(),1);assert_eq!(bytes[0],37);assert!((key==Pubkey::new_from_array([42;32]))!=cfg!(PCG_NEG_RETURN));}
struct Log{reply:Option<(Pubkey,Vec<u8>)>,calls:u8}
fn reply_window(log:&mut Log)->Option<(Pubkey,Vec<u8>)>{log.calls+=1;log.reply.take()}
// Literal frozen return expression, with only the SDK cut given its local log.
fn get_window(log:&mut Log)->Option<(Pubkey,Vec<u8>)>{reply_window(log)}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn owned_reply_window(){
 let n:usize=kani::any();kani::assume(n<=1024);let k:usize=kani::any();if n>0{kani::assume(k<n);}else{kani::assume(k==0);}
 let mut bytes=alloc::vec![0u8;n];if n>0{bytes[k]=kani::any();}let pointer=bytes.as_ptr();let capacity=bytes.capacity();let old=if n>0{bytes[k]}else{0};let key:[u8;32]=kani::any();let some:bool=kani::any();
 let mut log=Log{reply:if some{Some((Pubkey::new_from_array(key),bytes))}else{None},calls:0};
 let got=get_window(&mut log);assert_eq!(log.calls,1);assert!(log.reply.is_none());
 match got{None=>assert!(!some),Some((mut who,data))=>{assert!(some);if cfg!(PCG_NEG_RETURN){who=Pubkey::new_from_array([key[0]^1,key[1],key[2],key[3],key[4],key[5],key[6],key[7],key[8],key[9],key[10],key[11],key[12],key[13],key[14],key[15],key[16],key[17],key[18],key[19],key[20],key[21],key[22],key[23],key[24],key[25],key[26],key[27],key[28],key[29],key[30],key[31]]);}assert_eq!(who,Pubkey::new_from_array(key));assert_eq!(data.as_ptr(),pointer);assert_eq!(data.len(),n);assert_eq!(data.capacity(),capacity);if n>0{assert_eq!(data[k],old);}}}
}
