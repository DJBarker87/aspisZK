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

struct LengthLog{count:u8,account:*const OwnedAccount,input:*const Result<usize,ProgramError>,ok:bool,n:usize,borrow:bool}
fn length_empty()->LengthLog{LengthLog{count:0,account:core::ptr::null(),input:core::ptr::null(),ok:false,n:0,borrow:false}}
fn length_oracle(a:&OwnedAccount,l:&mut LengthLog)->Result<usize,ProgramError>{
 assert!(matches!(&a.length,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData)));
 l.count+=1;l.account=a;l.input=&a.length;l.ok=kani::any();l.n=kani::any();l.borrow=kani::any();
 if l.ok{Ok(l.n)}else if l.borrow{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)}
}
fn checkpoint_cut(account:&OwnedAccount,program_id:&Pubkey,writable:bool,l:&mut LengthLog)->ProgramResult{
 if account.owner()!=program_id || account.is_signer || account.executable
  || account.is_writable!=writable
  || length_oracle(account,l)?!=verifier::checkpoint_size(Variant::S2){return Err(ProgramError::InvalidAccountData);}
 Ok(())
}
fn checkpoint_association(a:&OwnedAccount,p:&Pubkey,w:bool,l:&LengthLog,r:&ProgramResult)->bool{
 if a.owner!=*p||a.is_signer||a.executable||a.is_writable!=w{
  l.count==0&&matches!(r,Err(ProgramError::InvalidAccountData))
 }else{
  l.count==1&&l.account==a as *const OwnedAccount&&l.input==&a.length as *const Result<usize,ProgramError>&&
  if !l.ok{if l.borrow{matches!(r,Err(ProgramError::AccountBorrowFailed))}else{matches!(r,Err(ProgramError::InvalidAccountData))}}
  else if l.n!=1768{matches!(r,Err(ProgramError::InvalidAccountData))}else{r.is_ok()}
 }
}
#[kani::requires(l.count==0 && matches!(&a.length,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData)))]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn checkpoint_packet(a:&OwnedAccount,p:&Pubkey,w:bool,l:&mut LengthLog)->bool{let r=checkpoint_cut(a,p,w,l);checkpoint_association(a,p,w,l,&r)}
#[kani::proof_for_contract(checkpoint_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_logging(){let mut a=account();let shape:u8=kani::any();kani::assume(shape<3);a.length=if shape==0{Ok(kani::any())}else if shape==1{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)};let p=Pubkey::new_from_array(kani::any());let mut l=length_empty();let _=checkpoint_packet(&a,&p,kani::any(),&mut l);}
#[kani::requires(l.count==0 && matches!(&a.length,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData)))]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn checkpoint_corrupt_packet(a:&OwnedAccount,p:&Pubkey,w:bool,l:&mut LengthLog)->bool{let r=checkpoint_cut(a,p,w,l);if l.count==1{l.ok=!l.ok;}checkpoint_association(a,p,w,l,&r)}
#[kani::proof_for_contract(checkpoint_corrupt_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_logging_corrupt(){let mut a=account();a.is_signer=false;a.executable=false;let w=a.is_writable;let mut l=length_empty();let _=checkpoint_corrupt_packet(&a,&a.owner,w,&mut l);}

#[kani::requires(previous<index && index<3)]
#[kani::ensures(|r| *r)] #[kani::modifies()]
fn prefix_embedding_packet(a:&[OwnedAccount;3],index:usize,previous:usize)->bool{
 let original=[&a[0],&a[1],&a[2]];
 let extended=[&a[0],&a[1],&a[2],&a[0],&a[0],&a[0],&a[0]];
 core::ptr::eq(original[previous],extended[previous])&&core::ptr::eq(original[index],extended[index])
}
#[kani::proof_for_contract(prefix_embedding_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn distinct_prefix_embedding(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,3,_>(|_|{let b=account();core::mem::ManuallyDrop::into_inner(b)}));let i:usize=kani::any();let p:usize=kani::any();kani::assume(p<i&&i<3);let _=prefix_embedding_packet(&a,i,p);}
#[kani::requires(previous<index && index<3)]
#[kani::ensures(|r| *r)] #[kani::modifies()]
fn prefix_embedding_corrupt_packet(a:&[OwnedAccount;3],index:usize,previous:usize)->bool{
 let original=[&a[0],&a[1],&a[2]];
 let extended=[&a[1],&a[1],&a[2],&a[0],&a[0],&a[0],&a[0]];
 core::ptr::eq(original[previous],extended[previous])&&core::ptr::eq(original[index],extended[index])
}
#[kani::proof_for_contract(prefix_embedding_corrupt_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn distinct_prefix_embedding_corrupt(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,3,_>(|_|{let b=account();core::mem::ManuallyDrop::into_inner(b)}));let i:usize=kani::any();let p:usize=kani::any();kani::assume(p<i&&i<3);let _=prefix_embedding_corrupt_packet(&a,i,p);}

// After-copy continuation: the child reply allocation already exists in pre-state.
// modifies(record) permits the record/header move, not writes to its separate buffer.
struct ReturnLog{reply:Vec<u8>,count:u8,src:*const u8,len:usize,out:*const u8,out_len:usize,out_cap:usize}
fn returned_oracle(data:&[u8],l:&mut ReturnLog)->Vec<u8>{
 l.count+=1;l.src=data.as_ptr();l.len=data.len();let v=core::mem::take(&mut l.reply);l.out=v.as_ptr();l.out_len=v.len();l.out_cap=v.capacity();v
}
fn returned_header_cut(data:&[u8],key:&Pubkey,owner:&Pubkey,s:bool,w:bool,e:bool,l:&mut ReturnLog)->OwnedAccount{
 let length=data.len();let bytes=Ok(returned_oracle(data,l));
 OwnedAccount{key:*key,owner:*owner,is_signer:s,is_writable:w,executable:e,length:Ok(length),bytes}
}
fn returned_association(data:&[u8],k:&Pubkey,o:&Pubkey,s:bool,w:bool,e:bool,l:&ReturnLog,r:&OwnedAccount)->bool{
 r.key==*k&&r.owner==*o&&r.is_signer==s&&r.is_writable==w&&r.executable==e&&matches!(r.length,Ok(n)if n==data.len())&&l.count==1&&l.src==data.as_ptr()&&l.len==data.len()&&l.out!=data.as_ptr()&&
 match &r.bytes{Ok(v)=>v.as_ptr()==l.out&&v.len()==l.out_len&&v.capacity()==l.out_cap,_=>false}
}
#[kani::requires(l.count==0 && data.len()==l.reply.len() && !data.is_empty())]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn returned_header_packet(data:&[u8],k:&Pubkey,o:&Pubkey,s:bool,w:bool,e:bool,l:&mut ReturnLog)->bool{
 let r=core::mem::ManuallyDrop::new(returned_header_cut(data,k,o,s,w,e,l));returned_association(data,k,o,s,w,e,l,&r)
}
#[kani::requires(l.count==0 && data.len()==l.reply.len() && !data.is_empty())]
#[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn returned_corrupt_packet(data:&[u8],k:&Pubkey,o:&Pubkey,s:bool,w:bool,e:bool,l:&mut ReturnLog)->bool{
 let mut r=core::mem::ManuallyDrop::new(returned_header_cut(data,k,o,s,w,e,l));if let Ok(v)=&mut r.bytes{v[0]^=1;}returned_association(data,k,o,s,w,e,l,&r)
}
macro_rules! returned_instance {
 ($pass:ident,$bad:ident,$n:expr)=>{
 #[kani::proof_for_contract(returned_header_packet)] #[kani::unwind(35)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 fn $pass(){let k=Pubkey::new_from_array(kani::any());let o=Pubkey::new_from_array(kani::any());let src=kani::vec::exact_vec::<u8,$n>();let reply=kani::vec::exact_vec::<u8,$n>();let mut l=ReturnLog{reply,count:0,src:core::ptr::null(),len:0,out:core::ptr::null(),out_len:0,out_cap:0};let _=returned_header_packet(&src,&k,&o,kani::any(),kani::any(),kani::any(),&mut l);}
 #[kani::proof_for_contract(returned_corrupt_packet)] #[kani::unwind(35)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 fn $bad(){let k=Pubkey::new_from_array(kani::any());let o=Pubkey::new_from_array(kani::any());let src=kani::vec::exact_vec::<u8,$n>();let reply=kani::vec::exact_vec::<u8,$n>();let mut l=ReturnLog{reply,count:0,src:core::ptr::null(),len:0,out:core::ptr::null(),out_len:0,out_cap:0};let _=returned_corrupt_packet(&src,&k,&o,kani::any(),kani::any(),kani::any(),&mut l);}
 }
}
returned_instance!(returned_header_58295,returned_header_58295_corrupt,58295);
returned_instance!(returned_header_1768,returned_header_1768_corrupt,1768);
returned_instance!(returned_header_1880,returned_header_1880_corrupt,1880);
returned_instance!(returned_header_384,returned_header_384_corrupt,384);
returned_instance!(returned_header_192,returned_header_192_corrupt,192);
returned_instance!(returned_header_768,returned_header_768_corrupt,768);
returned_instance!(returned_header_128,returned_header_128_corrupt,128);
returned_instance!(returned_header_256,returned_header_256_corrupt,256);
returned_instance!(returned_header_320,returned_header_320_corrupt,320);

#[kani::requires(!src.is_empty() && src.len()<=58295)]
#[kani::ensures(|r| *r)] #[kani::modifies()]
fn alloc_header_packet(src:&[u8])->bool{let v=core::mem::ManuallyDrop::new(Vec::<u8>::with_capacity(src.len()));v.len()==0&&v.capacity()>=src.len()&&v.as_ptr()!=src.as_ptr()}
#[kani::proof_for_contract(alloc_header_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn to_vec_alloc_header(){let mut src=kani::vec::exact_vec::<u8,58295>();let n:usize=kani::any();kani::assume(n>0&&n<=58295);src.truncate(n);let _=alloc_header_packet(&src);}
#[kani::requires(!src.is_empty() && src.len()<=58295)]
#[kani::ensures(|r| *r)] #[kani::modifies()]
fn alloc_header_corrupt_packet(src:&[u8],external:&mut u8)->bool{let v=core::mem::ManuallyDrop::new(Vec::<u8>::with_capacity(src.len()));*external^=1;v.len()==0&&v.capacity()>=src.len()&&v.as_ptr()!=src.as_ptr()}
#[kani::proof_for_contract(alloc_header_corrupt_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn to_vec_alloc_header_corrupt(){let src=kani::vec::exact_vec::<u8,128>();let mut external:u8=kani::any();let _=alloc_header_corrupt_packet(&src,&mut external);}

#[kani::ensures(|r| *r)] #[kani::modifies(dst)]
fn byte_window_packet(src:&u8,dst:&mut core::mem::MaybeUninit<u8>)->bool{unsafe{core::ptr::copy_nonoverlapping(src as *const u8,dst.as_mut_ptr(),1)};unsafe{dst.assume_init_read()==*src}}
#[kani::proof_for_contract(byte_window_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn to_vec_byte_window(){let src:u8=kani::any();let initialized:bool=kani::any();let mut dst=if initialized{core::mem::MaybeUninit::new(kani::any())}else{core::mem::MaybeUninit::uninit()};let _=byte_window_packet(&src,&mut dst);}
#[kani::ensures(|r| *r)] #[kani::modifies(dst)]
fn byte_window_corrupt_packet(src:&u8,dst:&mut core::mem::MaybeUninit<u8>)->bool{unsafe{core::ptr::copy_nonoverlapping(src as *const u8,dst.as_mut_ptr(),1)};dst.write(*src^1);unsafe{dst.assume_init_read()==*src}}
#[kani::proof_for_contract(byte_window_corrupt_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn to_vec_byte_window_corrupt(){let src:u8=kani::any();let mut dst=core::mem::MaybeUninit::uninit();let _=byte_window_corrupt_packet(&src,&mut dst);}

#[kani::requires(v.len()==0 && n>0 && n<=v.capacity() && n<=58295)]
#[kani::ensures(|r| *r)] #[kani::modifies(v)]
unsafe fn set_len_packet(v:&mut Vec<u8>,n:usize)->bool{let old=v.as_ptr();let cap=v.capacity();unsafe{v.set_len(n)};v.as_ptr()==old&&v.capacity()==cap&&v.len()==n}
#[kani::proof_for_contract(set_len_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn to_vec_finalize(){let mut v=kani::vec::exact_vec::<u8,58295>();let n:usize=kani::any();kani::assume(n>0&&n<=58295);v.clear();unsafe{let _=set_len_packet(&mut v,n);}}
#[kani::requires(v.len()==0 && n>0 && n<=v.capacity() && n<=58295)]
#[kani::ensures(|r| *r)] #[kani::modifies(v)]
unsafe fn set_len_corrupt_packet(v:&mut Vec<u8>,n:usize)->bool{let old=v.as_ptr();let cap=v.capacity();unsafe{v.set_len(n)};v[0]^=1;v.as_ptr()==old&&v.capacity()==cap&&v.len()==n}
#[kani::proof_for_contract(set_len_corrupt_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn to_vec_finalize_corrupt(){let mut v=kani::vec::exact_vec::<u8,128>();v.clear();unsafe{let _=set_len_corrupt_packet(&mut v,128);}}

// Exact authentication guard prefix. Continuation is a staged boundary.
struct AuthLog { count:usize, accounts:[*const OwnedAccount;7], owner:*const Pubkey,
 expected:[*const Pubkey;6], receiver:[*const OwnedAccount;6], ok:[bool;6], borrow:bool }
fn auth_empty()->AuthLog{AuthLog{count:0,accounts:[core::ptr::null();7],owner:core::ptr::null(),expected:[core::ptr::null();6],receiver:[core::ptr::null();6],ok:[false;6],borrow:false}}
fn auth_oracle(a:&OwnedAccount,k:*const Pubkey,stage:usize,l:&mut AuthLog)->ProgramResult{
 assert_eq!(l.count,stage);l.count+=1;l.receiver[stage]=a;l.expected[stage]=k;l.ok[stage]=kani::any();
 if l.ok[stage]{Ok(())}else if stage==1{l.borrow=kani::any();if l.borrow{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)}}else if stage==5{Err(ProgramError::InvalidArgument)}else{Err(ProgramError::InvalidAccountData)}
}
fn auth_distinct_oracle(a:&[&OwnedAccount;7],l:&mut AuthLog)->ProgramResult{for i in 0..7{l.accounts[i]=a[i];}auth_oracle(a[0],core::ptr::null(),5,l)}
fn auth_prefix_cut(verifier_program:&Pubkey,accounts:&[OwnedAccount],pool_program:&Pubkey,l:&mut AuthLog)->ProgramResult{
 let [proof_account,master_account,checkpoint_account,lane_account,registry_account,entry_account,verifier_checkpoint]=accounts else{return Err(if accounts.len()<7{ProgramError::NotEnoughAccountKeys}else{ProgramError::InvalidArgument});};
 auth_oracle(proof_account,core::ptr::null(),0,l)?;
 auth_oracle(verifier_checkpoint,verifier_program,1,l)?;
 auth_oracle(master_account,pool_program,2,l)?;
 auth_oracle(checkpoint_account,pool_program,3,l)?;
 auth_oracle(lane_account,pool_program,4,l)?;
 auth_distinct_oracle(&[proof_account,master_account,checkpoint_account,lane_account,registry_account,entry_account,verifier_checkpoint],l)?;
 Ok(())
}
fn auth_trace(a:&[OwnedAccount],v:&Pubkey,p:&Pubkey,l:&AuthLog,r:&ProgramResult)->bool{
 if a.len()!=7{return l.count==0&&if a.len()<7{matches!(r,Err(ProgramError::NotEnoughAccountKeys))}else{matches!(r,Err(ProgramError::InvalidArgument))};}
 let selected=[0,6,1,2,3,0];
 for i in 0..l.count{if l.receiver[i]!=&a[selected[i]] as *const OwnedAccount{return false;}let expected=if i==1{v as *const Pubkey}else if i>=2&&i<=4{p as *const Pubkey}else{core::ptr::null()};if l.expected[i]!=expected{return false;}if !l.ok[i]{return l.count==i+1&&if i==1&&l.borrow{matches!(r,Err(ProgramError::AccountBorrowFailed))}else if i==5{matches!(r,Err(ProgramError::InvalidArgument))}else{matches!(r,Err(ProgramError::InvalidAccountData))};}}
 if l.count==6{for i in 0..7{if l.accounts[i]!=&a[i] as *const OwnedAccount{return false;}}r.is_ok()}else{false}
}
#[kani::requires(l.count==0&&a.len()==7)] #[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn auth_prefix_packet(a:&[OwnedAccount],v:&Pubkey,p:&Pubkey,l:&mut AuthLog)->bool{let r=auth_prefix_cut(v,a,p,l);auth_trace(a,v,p,l,&r)}
#[kani::proof_for_contract(auth_prefix_packet)] #[kani::unwind(9)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn auth_prefix(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|_|core::mem::ManuallyDrop::into_inner(account())));let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let mut l=auth_empty();auth_prefix_packet(&a[..],&v,&p,&mut l);}
#[kani::requires(l.count==0&&a.len()==7)] #[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn auth_corrupt0_packet(a:&[OwnedAccount],v:&Pubkey,p:&Pubkey,l:&mut AuthLog)->bool{let r=auth_prefix_cut(v,a,p,l);if l.count>0{l.receiver[0]=core::ptr::null();}auth_trace(a,v,p,l,&r)}
#[kani::proof_for_contract(auth_corrupt0_packet)] #[kani::unwind(9)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn auth_corrupt0(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|_|core::mem::ManuallyDrop::into_inner(account())));let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let mut l=auth_empty();auth_corrupt0_packet(&a[..],&v,&p,&mut l);}
#[kani::requires(l.count==0&&a.len()==7)] #[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn auth_corrupt1_packet(a:&[OwnedAccount],v:&Pubkey,p:&Pubkey,l:&mut AuthLog)->bool{let r=auth_prefix_cut(v,a,p,l);if l.count>1{l.receiver[1]=core::ptr::null();}auth_trace(a,v,p,l,&r)}
#[kani::proof_for_contract(auth_corrupt1_packet)] #[kani::unwind(9)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn auth_corrupt1(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|_|core::mem::ManuallyDrop::into_inner(account())));let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let mut l=auth_empty();auth_corrupt1_packet(&a[..],&v,&p,&mut l);}
#[kani::requires(l.count==0&&a.len()==7)] #[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn auth_corrupt2_packet(a:&[OwnedAccount],v:&Pubkey,p:&Pubkey,l:&mut AuthLog)->bool{let r=auth_prefix_cut(v,a,p,l);if l.count>2{l.receiver[2]=core::ptr::null();}auth_trace(a,v,p,l,&r)}
#[kani::proof_for_contract(auth_corrupt2_packet)] #[kani::unwind(9)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn auth_corrupt2(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|_|core::mem::ManuallyDrop::into_inner(account())));let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let mut l=auth_empty();auth_corrupt2_packet(&a[..],&v,&p,&mut l);}
#[kani::requires(l.count==0&&a.len()==7)] #[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn auth_corrupt3_packet(a:&[OwnedAccount],v:&Pubkey,p:&Pubkey,l:&mut AuthLog)->bool{let r=auth_prefix_cut(v,a,p,l);if l.count>3{l.receiver[3]=core::ptr::null();}auth_trace(a,v,p,l,&r)}
#[kani::proof_for_contract(auth_corrupt3_packet)] #[kani::unwind(9)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn auth_corrupt3(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|_|core::mem::ManuallyDrop::into_inner(account())));let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let mut l=auth_empty();auth_corrupt3_packet(&a[..],&v,&p,&mut l);}
#[kani::requires(l.count==0&&a.len()==7)] #[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn auth_corrupt4_packet(a:&[OwnedAccount],v:&Pubkey,p:&Pubkey,l:&mut AuthLog)->bool{let r=auth_prefix_cut(v,a,p,l);if l.count>4{l.receiver[4]=core::ptr::null();}auth_trace(a,v,p,l,&r)}
#[kani::proof_for_contract(auth_corrupt4_packet)] #[kani::unwind(9)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn auth_corrupt4(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|_|core::mem::ManuallyDrop::into_inner(account())));let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let mut l=auth_empty();auth_corrupt4_packet(&a[..],&v,&p,&mut l);}
#[kani::requires(l.count==0&&a.len()==7)] #[kani::ensures(|r| *r)] #[kani::modifies(l)]
fn auth_corrupt5_packet(a:&[OwnedAccount],v:&Pubkey,p:&Pubkey,l:&mut AuthLog)->bool{let r=auth_prefix_cut(v,a,p,l);if l.count>5{l.receiver[5]=core::ptr::null();}auth_trace(a,v,p,l,&r)}
#[kani::proof_for_contract(auth_corrupt5_packet)] #[kani::unwind(9)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn auth_corrupt5(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|_|core::mem::ManuallyDrop::into_inner(account())));let v=Pubkey::new_from_array(kani::any());let p=Pubkey::new_from_array(kani::any());let mut l=auth_empty();auth_corrupt5_packet(&a[..],&v,&p,&mut l);}
// Replacement for K052: one staged call, arbitrary pre-state and stage invariant.
struct GuardStepLog {count:usize,receiver:*const OwnedAccount,expected:*const Pubkey,ok:bool,borrow:bool}
fn guard_step(a:&OwnedAccount,k:*const Pubkey,stage:usize,l:&mut GuardStepLog)->ProgramResult{
 l.count+=1;l.receiver=a;l.expected=k;l.ok=kani::any();
 if l.ok{Ok(())}else if stage==1 {l.borrow=kani::any();if l.borrow{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)}}else if stage==5{Err(ProgramError::InvalidArgument)}else{Err(ProgramError::InvalidAccountData)}
}
fn guard_association(a:&OwnedAccount,k:*const Pubkey,stage:usize,l:&GuardStepLog,r:&ProgramResult)->bool{
 l.count==stage+1&&l.receiver==a as *const OwnedAccount&&l.expected==k&&if l.ok{r.is_ok()}else if stage==1&&l.borrow{matches!(r,Err(ProgramError::AccountBorrowFailed))}else if stage==5{matches!(r,Err(ProgramError::InvalidArgument))}else{matches!(r,Err(ProgramError::InvalidAccountData))}
}
#[kani::requires(stage<6&&l.count==stage)] #[kani::ensures(|r|*r)] #[kani::modifies(l)]
fn guard_packet(a:&OwnedAccount,k:*const Pubkey,stage:usize,l:&mut GuardStepLog)->bool{let r=guard_step(a,k,stage,l);guard_association(a,k,stage,l,&r)}
#[kani::proof_for_contract(guard_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn guard_native_step(){let a=account();let k=Pubkey::new_from_array(kani::any());let stage:usize=kani::any();kani::assume(stage<6);let mut l=GuardStepLog{count:stage,receiver:core::ptr::null(),expected:core::ptr::null(),ok:kani::any(),borrow:kani::any()};guard_packet(&a,if kani::any(){core::ptr::null()}else{&k},stage,&mut l);}
#[kani::requires(stage<6&&l.count==stage)] #[kani::ensures(|r|*r)] #[kani::modifies(l)]
fn guard_wrong_packet(a:&OwnedAccount,k:*const Pubkey,stage:usize,l:&mut GuardStepLog)->bool{let r=guard_step(a,k,stage,l);l.receiver=core::ptr::null();guard_association(a,k,stage,l,&r)}
#[kani::proof_for_contract(guard_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn guard_native_wrong(){let a=account();let k=Pubkey::new_from_array(kani::any());let stage:usize=kani::any();kani::assume(stage<6);let mut l=GuardStepLog{count:stage,receiver:core::ptr::null(),expected:core::ptr::null(),ok:kani::any(),borrow:kani::any()};guard_wrong_packet(&a,if kani::any(){core::ptr::null()}else{&k},stage,&mut l);}
// Exact KMX one-byte window, real typed SDK guard held across real allocation.
// This is not a to_vec replacement or a full snapshot certificate.
fn sdk_real_window<const N:usize>(leak:bool){
 let k=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut coins:u64=kani::any();let coins0=coins;let mut bytes=kani::vec::exact_vec::<u8,N>();let index:usize=kani::any();kani::assume(index<N);let selected=bytes[index];let a=AccountInfo::new(&k,false,false,&mut coins,&mut bytes,&owner,false,0);
 let external:bool=kani::any();let held=if external{Some(a.try_borrow_data().unwrap())}else{None};
 let guard=a.try_borrow_data().unwrap();let mut dst=Vec::<core::mem::MaybeUninit<u8>>::with_capacity(N);unsafe{dst.set_len(N);core::ptr::copy_nonoverlapping(guard.as_ptr().add(index),dst.as_mut_ptr().add(index).cast::<u8>(),1);assert_eq!(dst[index].assume_init_read(),selected);}
 if leak{core::mem::forget(guard)}else{drop(guard)}
 assert_eq!(a.try_borrow_mut_data().is_ok(),!external);drop(held);assert!(a.try_borrow_mut_data().is_ok());assert_eq!(a.lamports(),coins0);
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sdk_real_copy_window(){sdk_real_window::<128>(false);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sdk_real_copy_window_wrong(){sdk_real_window::<128>(true);}

macro_rules! sdk_window_instance {
 ($good:ident,$bad:ident,$n:expr)=>{
 #[kani::proof] #[kani::unwind(35)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 fn $good(){sdk_real_window::<$n>(false);}
 #[kani::proof] #[kani::unwind(35)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 fn $bad(){sdk_real_window::<$n>(true);}
 }
}
sdk_window_instance!(sdk_window_58295,sdk_window_58295_wrong,58295);
sdk_window_instance!(sdk_window_1768,sdk_window_1768_wrong,1768);
sdk_window_instance!(sdk_window_1880,sdk_window_1880_wrong,1880);
sdk_window_instance!(sdk_window_384,sdk_window_384_wrong,384);
sdk_window_instance!(sdk_window_192,sdk_window_192_wrong,192);
sdk_window_instance!(sdk_window_768,sdk_window_768_wrong,768);
sdk_window_instance!(sdk_window_256,sdk_window_256_wrong,256);
sdk_window_instance!(sdk_window_320,sdk_window_320_wrong,320);
// Same after-Clock::get continuation as deployed stage2; no syscall value proof.
fn clock_error(tag:u8,custom:u32)->ProgramError{match tag{
0=>ProgramError::Custom(custom),
1=>ProgramError::InvalidArgument,
2=>ProgramError::InvalidInstructionData,
3=>ProgramError::InvalidAccountData,
4=>ProgramError::AccountDataTooSmall,
5=>ProgramError::InsufficientFunds,
6=>ProgramError::IncorrectProgramId,
7=>ProgramError::MissingRequiredSignature,
8=>ProgramError::AccountAlreadyInitialized,
9=>ProgramError::UninitializedAccount,
10=>ProgramError::NotEnoughAccountKeys,
11=>ProgramError::AccountBorrowFailed,
12=>ProgramError::MaxSeedLengthExceeded,
13=>ProgramError::InvalidSeeds,
14=>ProgramError::BorshIoError(alloc::string::String::from("Unknown")),
15=>ProgramError::AccountNotRentExempt,
16=>ProgramError::UnsupportedSysvar,
17=>ProgramError::IllegalOwner,
18=>ProgramError::MaxAccountsDataAllocationsExceeded,
19=>ProgramError::InvalidRealloc,
20=>ProgramError::MaxInstructionTraceLengthExceeded,
21=>ProgramError::BuiltinProgramsMustConsumeComputeUnits,
22=>ProgramError::InvalidAccountOwner,
23=>ProgramError::ArithmeticOverflow,
24=>ProgramError::Immutable,
25=>ProgramError::IncorrectAuthority,
_=>unreachable!()}}
fn clock_error_descriptor(e:&ProgramError)->(u8,u32,*const u8,usize){match e{
ProgramError::Custom(n)=>(0,*n,core::ptr::null(),0),
ProgramError::InvalidArgument=>(1,0,core::ptr::null(),0),
ProgramError::InvalidInstructionData=>(2,0,core::ptr::null(),0),
ProgramError::InvalidAccountData=>(3,0,core::ptr::null(),0),
ProgramError::AccountDataTooSmall=>(4,0,core::ptr::null(),0),
ProgramError::InsufficientFunds=>(5,0,core::ptr::null(),0),
ProgramError::IncorrectProgramId=>(6,0,core::ptr::null(),0),
ProgramError::MissingRequiredSignature=>(7,0,core::ptr::null(),0),
ProgramError::AccountAlreadyInitialized=>(8,0,core::ptr::null(),0),
ProgramError::UninitializedAccount=>(9,0,core::ptr::null(),0),
ProgramError::NotEnoughAccountKeys=>(10,0,core::ptr::null(),0),
ProgramError::AccountBorrowFailed=>(11,0,core::ptr::null(),0),
ProgramError::MaxSeedLengthExceeded=>(12,0,core::ptr::null(),0),
ProgramError::InvalidSeeds=>(13,0,core::ptr::null(),0),
ProgramError::BorshIoError(s)=>(14,0,s.as_ptr(),s.len()),
ProgramError::AccountNotRentExempt=>(15,0,core::ptr::null(),0),
ProgramError::UnsupportedSysvar=>(16,0,core::ptr::null(),0),
ProgramError::IllegalOwner=>(17,0,core::ptr::null(),0),
ProgramError::MaxAccountsDataAllocationsExceeded=>(18,0,core::ptr::null(),0),
ProgramError::InvalidRealloc=>(19,0,core::ptr::null(),0),
ProgramError::MaxInstructionTraceLengthExceeded=>(20,0,core::ptr::null(),0),
ProgramError::BuiltinProgramsMustConsumeComputeUnits=>(21,0,core::ptr::null(),0),
ProgramError::InvalidAccountOwner=>(22,0,core::ptr::null(),0),
ProgramError::ArithmeticOverflow=>(23,0,core::ptr::null(),0),
ProgramError::Immutable=>(24,0,core::ptr::null(),0),
ProgramError::IncorrectAuthority=>(25,0,core::ptr::null(),0),
}}
fn clock_forward(input:Result<Clock,ProgramError>)->Result<u64,ProgramError>{match input{Ok(clock)=>Ok(clock.slot),Err(error)=>Err(error)}}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn clock_packet(input:Result<Clock,ProgramError>)->bool{
 let before=match &input{Ok(c)=>(true,c.slot,(0,0,core::ptr::null(),0)),Err(e)=>(false,0,clock_error_descriptor(e))};
 let r=core::mem::ManuallyDrop::new(clock_forward(input));match &*r{Ok(n)=>before.0&&*n==before.1,Err(e)=>!before.0&&clock_error_descriptor(e)==before.2}
}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn clock_wrong_packet(input:Result<Clock,ProgramError>)->bool{
 let before=match &input{Ok(c)=>(true,c.slot,(0,0,core::ptr::null(),0)),Err(e)=>(false,0,clock_error_descriptor(e))};
 let mut r=core::mem::ManuallyDrop::new(clock_forward(input));match &mut *r{Ok(n)=>*n^=1,Err(e)=>{let old=core::mem::replace(e,ProgramError::InvalidSeeds);core::mem::forget(old);}};match &*r{Ok(n)=>before.0&&*n==before.1,Err(e)=>!before.0&&clock_error_descriptor(e)==before.2}
}
fn clock_input()->Result<Clock,ProgramError>{let ok:bool=kani::any();if ok{Ok(Clock{slot:kani::any(),epoch_start_timestamp:kani::any(),epoch:kani::any(),leader_schedule_epoch:kani::any(),unix_timestamp:kani::any()})}else{let tag:u8=kani::any();kani::assume(tag<26);Err(clock_error(tag,kani::any()))}}
#[kani::proof_for_contract(clock_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn clock_exact_forward(){clock_packet(clock_input());}
#[kani::proof_for_contract(clock_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn clock_corrupt_forward(){clock_wrong_packet(clock_input());}

const NHJ_POOL_DEV:[u8;32]=[160,19,98,42,240,202,109,154,218,233,162,167,169,176,187,66,122,69,190,75,195,45,233,50,40,58,26,66,26,133,145,52];
const NHJ_REGISTRY_DEV:[u8;32]=[131,9,163,201,153,45,35,222,189,104,139,224,185,96,72,135,226,88,106,68,10,156,60,72,82,28,53,49,227,146,232,171];
fn registry_header_cut(pool_program:&Pubkey,policy:&aspis_statement::pool_v1::VerifierPolicyV1)->ProgramResult{
 if pool_program.to_bytes()!=pool_program_id()||policy.flags&POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY==0||policy.registry_program!=registry_program_id()||policy.registry_authority!=[0u8;32]||policy.policy_binding!=AUDIT_POLICY_BINDING{return Err(ProgramError::InvalidAccountData);}Ok(())
}
fn registry_expected(pool:&Pubkey,policy:&aspis_statement::pool_v1::VerifierPolicyV1)->bool{pool.to_bytes()==NHJ_POOL_DEV&&policy.flags&POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY!=0&&policy.registry_program==NHJ_REGISTRY_DEV&&policy.registry_authority==[0;32]&&policy.policy_binding==[7;32]}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_header_packet(pool:&Pubkey,policy:&aspis_statement::pool_v1::VerifierPolicyV1)->bool{let r=registry_header_cut(pool,policy);let expected=registry_expected(pool,policy);if expected{r.is_ok()}else{matches!(r,Err(ProgramError::InvalidAccountData))}}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_header_wrong_packet(pool:&Pubkey,policy:&aspis_statement::pool_v1::VerifierPolicyV1)->bool{let r=registry_header_cut(pool,policy);let expected=registry_expected(pool,policy);if expected{matches!(r,Err(ProgramError::InvalidAccountData))}else{r.is_ok()}}
fn registry_policy()->aspis_statement::pool_v1::VerifierPolicyV1{aspis_statement::pool_v1::VerifierPolicyV1{flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()}}
#[kani::proof_for_contract(registry_header_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_header(){let p=Pubkey::new_from_array(kani::any());registry_header_packet(&p,&registry_policy());}
#[kani::proof_for_contract(registry_header_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_header_wrong(){let p=Pubkey::new_from_array(kani::any());registry_header_wrong_packet(&p,&registry_policy());}
// Domain repair: finalize requires cap<=58295; cap>=n alone did not establish it.
#[kani::requires(n>0&&n<=58295)] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn allocation_exact_packet(n:usize)->bool{let v=core::mem::ManuallyDrop::new(Vec::<u8>::with_capacity(n));v.len()==0&&v.capacity()==n}
#[kani::proof_for_contract(allocation_exact_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn allocation_exact(){let n:usize=kani::any();kani::assume(n>0&&n<=58295);allocation_exact_packet(n);}
#[kani::requires(n>0&&n<=58295)] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn allocation_exact_wrong_packet(n:usize,cell:&mut u8)->bool{let v=core::mem::ManuallyDrop::new(Vec::<u8>::with_capacity(n));*cell^=1;v.len()==0&&v.capacity()==n}
#[kani::proof_for_contract(allocation_exact_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn allocation_exact_wrong(){let n:usize=kani::any();kani::assume(n>0&&n<=58295);let mut cell=kani::any();allocation_exact_wrong_packet(n,&mut cell);}
// Unit/reference contract shape; frame-only summary is used only for context.
// The independent exact byte value law remains K039/K040 and NHJ_CopyPacket.
#[kani::ensures(|_|true)] #[kani::modifies(dst)]
fn copy_unit_frame(src:&u8,dst:&mut core::mem::MaybeUninit<u8>){unsafe{core::ptr::copy_nonoverlapping(src,dst.as_mut_ptr(),1);}}
#[kani::proof_for_contract(copy_unit_frame)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_unit_real(){let src:u8=kani::any();let mut dst=if kani::any(){core::mem::MaybeUninit::new(kani::any())}else{core::mem::MaybeUninit::uninit()};copy_unit_frame(&src,&mut dst);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_unit_real_caller(){let src:u8=kani::any();let mut dst=core::mem::MaybeUninit::uninit();copy_unit_frame(&src,&mut dst);assert_eq!(unsafe{dst.assume_init_read()},src);}
#[kani::proof] #[kani::unwind(35)] #[kani::stub_verified(copy_unit_frame)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_unit_unimplied(){let src:u8=kani::any();let mut dst=core::mem::MaybeUninit::uninit();copy_unit_frame(&src,&mut dst);assert_eq!(unsafe{dst.assume_init_read()},src);}
#[kani::ensures(|_|unsafe{dst.assume_init_read()!=*src})] #[kani::modifies(dst)]
fn copy_unit_invert_packet(src:&u8,dst:&mut core::mem::MaybeUninit<u8>){unsafe{core::ptr::copy_nonoverlapping(src,dst.as_mut_ptr(),1);}}
#[kani::proof_for_contract(copy_unit_invert_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_unit_invert(){let src:u8=kani::any();let mut dst=core::mem::MaybeUninit::uninit();copy_unit_invert_packet(&src,&mut dst);}
#[kani::ensures(|_|true)] #[kani::modifies(dst)]
fn copy_unit_modifies_packet(src:&u8,dst:&mut core::mem::MaybeUninit<u8>,other:&mut u8){unsafe{core::ptr::copy_nonoverlapping(src,dst.as_mut_ptr(),1);}*other^=1;}
#[kani::proof_for_contract(copy_unit_modifies_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_unit_modifies(){let src:u8=kani::any();let mut dst=core::mem::MaybeUninit::uninit();let mut other=kani::any();copy_unit_modifies_packet(&src,&mut dst,&mut other);}
// K064 replacement: context checks only; byte value is discharged separately.
// The real Vec<u8> keeps len=0; its spare-capacity window is MaybeUninit<u8>.
fn sdk_summary_window<const N:usize>(leak:bool,wrong_argument:bool){
 let k=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut coins:u64=kani::any();let coins0=coins;let mut bytes=kani::vec::exact_vec::<u8,N>();let index:usize=kani::any();kani::assume(index<N);let a=AccountInfo::new(&k,kani::any(),kani::any(),&mut coins,&mut bytes,&owner,kani::any(),kani::any());
 let external:bool=kani::any();let held=if external{Some(a.try_borrow_data().unwrap())}else{None};
 let guard=a.try_borrow_data().unwrap();let source=guard.as_ptr();let mut dst=Vec::<u8>::with_capacity(N);let destination=dst.as_mut_ptr();
 let selected=if wrong_argument{if index+1<N{index+1}else{0}}else{index};
 let src=&guard[selected];let output=&mut dst.spare_capacity_mut()[index];
 assert_eq!(src as *const u8,source.wrapping_add(index));assert_eq!(output.as_mut_ptr(),destination.wrapping_add(index));
 copy_unit_frame(src,output);
 assert!(dst.len()==0&&dst.capacity()>=N);
 if leak{core::mem::forget(guard)}else{drop(guard)}
 assert_eq!(a.try_borrow_mut_data().is_ok(),!external);drop(held);assert!(a.try_borrow_mut_data().is_ok());assert_eq!(a.lamports(),coins0);
}
#[kani::proof] #[kani::unwind(35)] #[kani::stub_verified(copy_unit_frame)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sdk_summary_max(){sdk_summary_window::<58295>(false,false);}
#[kani::proof] #[kani::unwind(35)] #[kani::stub_verified(copy_unit_frame)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sdk_summary_max_drop_wrong(){sdk_summary_window::<58295>(true,false);}
#[kani::proof] #[kani::unwind(35)] #[kani::stub_verified(copy_unit_frame)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sdk_summary_max_argument_wrong(){sdk_summary_window::<58295>(false,true);}

fn sdk_summary_family(count:usize,leak:bool,wrong_argument:bool){
 let k=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut coins:u64=kani::any();let coins0=coins;let mut bytes=kani::vec::exact_vec::<u8,58295>();bytes.truncate(count);let index:usize=kani::any();kani::assume(index<count);let a=AccountInfo::new(&k,kani::any(),kani::any(),&mut coins,&mut bytes,&owner,kani::any(),kani::any());
 let external:bool=kani::any();let held=if external{Some(a.try_borrow_data().unwrap())}else{None};
 let guard=a.try_borrow_data().unwrap();let source=guard.as_ptr();let mut dst=Vec::<u8>::with_capacity(count);let destination=dst.as_mut_ptr();
 let selected=if wrong_argument{if index+1<count{index+1}else{0}}else{index};
 let src=&guard[selected];let output=&mut dst.spare_capacity_mut()[index];
 assert_eq!(src as *const u8,source.wrapping_add(index));assert_eq!(output.as_mut_ptr(),destination.wrapping_add(index));
 copy_unit_frame(src,output);
 assert!(dst.len()==0&&dst.capacity()>=count);
 if leak{core::mem::forget(guard)}else{drop(guard)}
 assert_eq!(a.try_borrow_mut_data().is_ok(),!external);drop(held);assert!(a.try_borrow_mut_data().is_ok());assert_eq!(a.lamports(),coins0);
}
#[kani::proof] #[kani::unwind(35)] #[kani::stub_verified(copy_unit_frame)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sdk_summary_all_lengths(){let count:usize=kani::any();kani::assume(count>0&&count<=58295);sdk_summary_family(count,false,false);}
#[kani::proof] #[kani::unwind(35)] #[kani::stub_verified(copy_unit_frame)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sdk_summary_all_lengths_drop_wrong(){let count:usize=kani::any();kani::assume(count>0&&count<=58295);sdk_summary_family(count,true,false);}
#[kani::proof] #[kani::unwind(35)] #[kani::stub_verified(copy_unit_frame)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sdk_summary_all_lengths_argument_wrong(){let count:usize=kani::any();kani::assume(count>0&&count<=58295);sdk_summary_family(count,false,true);}
fn snapshot_selected(length:usize,length1:usize,length2:usize)->bool{length==length1||length==length2}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn snapshot_selected_packet(length:usize,length1:usize,length2:usize)->bool{let actual=snapshot_selected(length,length1,length2);let natural=(length as u128)==(length1 as u128)||(length as u128)==(length2 as u128);actual==natural}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn snapshot_selected_wrong_packet(length:usize,length1:usize,length2:usize)->bool{let actual=!snapshot_selected(length,length1,length2);let natural=(length as u128)==(length1 as u128)||(length as u128)==(length2 as u128);actual==natural}
#[kani::proof_for_contract(snapshot_selected_packet)]
fn snapshot_selected_words(){snapshot_selected_packet(kani::any(),kani::any(),kani::any());}
#[kani::proof_for_contract(snapshot_selected_wrong_packet)]
fn snapshot_selected_words_wrong(){snapshot_selected_wrong_packet(kani::any(),kani::any(),kani::any());}
fn rejected_construct(k:&Pubkey,o:&Pubkey,s:bool,w:bool,e:bool,length:usize)->OwnedAccount{OwnedAccount{key:*k,owner:*o,is_signer:s,is_writable:w,executable:e,length:Ok(length),bytes:Err(ProgramError::InvalidAccountData)}}
fn rejected_construct_matches(r:&OwnedAccount,k:&Pubkey,o:&Pubkey,s:bool,w:bool,e:bool,length:usize)->bool{r.key==*k&&r.owner==*o&&r.is_signer==s&&r.is_writable==w&&r.executable==e&&matches!(r.length,Ok(n)if n==length)&&matches!(r.bytes,Err(ProgramError::InvalidAccountData))}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn rejected_construct_packet(k:&Pubkey,o:&Pubkey,s:bool,w:bool,e:bool,length:usize)->bool{let r=core::mem::ManuallyDrop::new(rejected_construct(k,o,s,w,e,length));rejected_construct_matches(&r,k,o,s,w,e,length)}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn rejected_construct_wrong_packet(k:&Pubkey,o:&Pubkey,s:bool,w:bool,e:bool,length:usize)->bool{let mut r=core::mem::ManuallyDrop::new(rejected_construct(k,o,s,w,e,length));let mut key=r.key.to_bytes();key[0]^=1;r.key=Pubkey::new_from_array(key);rejected_construct_matches(&r,k,o,s,w,e,length)}
#[kani::proof_for_contract(rejected_construct_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn rejected_construct_all_words(){let k=Pubkey::new_from_array(kani::any());let o=Pubkey::new_from_array(kani::any());rejected_construct_packet(&k,&o,kani::any(),kani::any(),kani::any(),kani::any());}
#[kani::proof_for_contract(rejected_construct_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn rejected_construct_all_words_wrong(){let k=Pubkey::new_from_array(kani::any());let o=Pubkey::new_from_array(kani::any());rejected_construct_wrong_packet(&k,&o,kani::any(),kani::any(),kani::any(),kani::any());}
// Unbounded descriptor length + one4-byte window; no fake large slice.
// Frozen classifier runs on the exact read window in each length class.
fn admitted_header(length:usize,window:&[u8;4])->bool{(length==2&&crate::pool_route::admitted(&window[..2]))||(length>=4&&crate::pool_route::admitted(&window[..]))}
fn admitted_header_ref(length:usize,window:&[u8;4])->bool{((length as u128)==2&&window[0]==3&&(window[1]==10||window[1]==11))||((length as u128)>=4&&*window==*b"ASQ8")}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn admitted_header_packet(length:usize,window:&[u8;4])->bool{admitted_header(length,window)==admitted_header_ref(length,window)}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn admitted_header_wrong_packet(length:usize,window:&[u8;4])->bool{let mut changed=*window;changed[0]^=1;admitted_header(length,&changed)==admitted_header_ref(length,window)}
#[kani::proof_for_contract(admitted_header_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn admitted_all_header_words(){let length:usize=kani::any();let window:[u8;4]=kani::any();admitted_header_packet(length,&window);}
#[kani::proof_for_contract(admitted_header_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn admitted_all_header_words_wrong(){let length:usize=kani::any();let window:[u8;4]=kani::any();admitted_header_wrong_packet(length,&window);}
// Byte-exact admitted_ref body from the pinned reused NCO reference.
pub fn admitted_ref(data:&[u8])->bool{(data.len()==2 && data[0]==3 && (data[1]==10 || data[1]==11)) || (data.len()>=4 && data[0]==65 && data[1]==83 && data[2]==81 && data[3]==56)}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn route_two_packet(window:&[u8;2])->bool{crate::pool_route::admitted(&window[..])==admitted_ref(&window[..])}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn route_two_wrong_packet(window:&[u8;2])->bool{let mut changed=*window;changed[0]^=1;crate::pool_route::admitted(&changed[..])==admitted_ref(&window[..])}
#[kani::proof_for_contract(route_two_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn route_physical_two(){let window:[u8;2]=kani::any();route_two_packet(&window);}
#[kani::proof_for_contract(route_two_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn route_physical_two_wrong(){let window:[u8;2]=kani::any();route_two_wrong_packet(&window);}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn route_zero_packet(one:&[u8;1],three:&[u8;3])->bool{!crate::pool_route::admitted(&[])&&!crate::pool_route::admitted(&one[..])&&!crate::pool_route::admitted(&three[..])}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn route_zero_wrong_packet(one:&[u8;1],three:&[u8;3])->bool{crate::pool_route::admitted(&[])||crate::pool_route::admitted(&one[..])||crate::pool_route::admitted(&three[..])}
#[kani::proof_for_contract(route_zero_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn route_physical_zero(){let one:[u8;1]=kani::any();let three:[u8;3]=kani::any();route_zero_packet(&one,&three);}
#[kani::proof_for_contract(route_zero_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn route_physical_zero_wrong(){let one:[u8;1]=kani::any();let three:[u8;3]=kani::any();route_zero_wrong_packet(&one,&three);}
