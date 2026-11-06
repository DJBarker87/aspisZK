from pathlib import Path
import difflib,subprocess
E=Path(__file__).resolve().parent
text=r'''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::requires(!bytes.is_empty()&&bytes.len()<=58295)]
#[kani::modifies(bytes)]
#[kani::ensures(|r|*r==0)]
fn havoc_bytes(bytes:&mut [u8;58295])->u8 {let _=bytes;0}
#[kani::requires(!bytes.is_empty()&&bytes.len()<=58295)]
#[kani::modifies(bytes)]
#[kani::ensures(|r|*r==1)]
fn havoc_inverse(bytes:&mut [u8;58295])->u8 {let _=bytes;0}
#[kani::requires(!bytes.is_empty())]
#[kani::modifies(bytes)]
#[kani::ensures(|r|*r==0)]
fn shape_effect(bytes:&mut [u8;58295])->u8 {bytes[0]=1;0}
#[kani::requires(!bytes.is_empty())]
#[kani::modifies(bytes)]
#[kani::ensures(|r|*r==1)]
fn shape_effect_inverse(bytes:&mut [u8;58295])->u8 {bytes[0]=1;0}
#[kani::requires(!bytes.is_empty())]
#[kani::modifies()]
#[kani::ensures(|r|*r==0)]
fn shape_modifies_bad(bytes:&mut [u8;58295])->u8 {bytes[0]=1;0}
#[kani::proof_for_contract(havoc_bytes)]#[kani::unwind(129)]
fn seed_contract(){let n:usize=kani::any();kani::assume(n>0&&n<=58295);let mut bytes=vec![0u8;58295];let a:&mut[u8;58295]=bytes.as_mut_slice().try_into().unwrap();let _=havoc_bytes(a);}
#[kani::proof_for_contract(havoc_inverse)]#[kani::unwind(129)]
fn seed_inverse_control(){let n:usize=kani::any();kani::assume(n>0&&n<=58295);let mut bytes=vec![0u8;58295];let a:&mut[u8;58295]=bytes.as_mut_slice().try_into().unwrap();let _=havoc_inverse(a);}
#[kani::proof_for_contract(shape_effect)]#[kani::unwind(129)]
fn effect_contract(){let mut bytes=vec![0u8;58295];let a:&mut[u8;58295]=bytes.as_mut_slice().try_into().unwrap();let _=shape_effect(a);}
#[kani::proof_for_contract(shape_effect_inverse)]#[kani::unwind(129)]
fn effect_inverse_control(){let mut bytes=vec![0u8;58295];let a:&mut[u8;58295]=bytes.as_mut_slice().try_into().unwrap();let _=shape_effect_inverse(a);}
#[kani::proof]#[kani::unwind(129)]
fn shape_real_body(){let mut bytes=vec![0u8;58295];let a:&mut[u8;58295]=bytes.as_mut_slice().try_into().unwrap();let r=shape_effect(a);assert_eq!(bytes[0],1);assert_eq!(r,0);}
#[kani::proof]#[kani::unwind(129)]#[kani::stub_verified(shape_effect)]
fn shape_unimplied_control(){let mut bytes=vec![0u8;58295];let a:&mut[u8;58295]=bytes.as_mut_slice().try_into().unwrap();let r=shape_effect(a);assert_eq!(bytes[0],1);assert_eq!(r,0);}
#[kani::proof_for_contract(shape_modifies_bad)]#[kani::unwind(129)]
fn shape_modifies_control(){let mut bytes=vec![0u8;58295];let a:&mut[u8;58295]=bytes.as_mut_slice().try_into().unwrap();let _=shape_modifies_bad(a);}
fn havoc_frame<const WRONG:bool>(){
 let mut data=vec![0u8;58295];let guard=vec![73u8;1];let p=data.as_ptr();let cap=data.capacity();
 let a:&mut[u8;58295]=data.as_mut_slice().try_into().unwrap();havoc_bytes(a);
 assert!((guard[0]==73&&data.as_ptr()==p&&data.len()==58295&&data.capacity()==cap)!=WRONG,"NLM whole-allocation initializer preserves caller metadata and disjoint allocation");
}
#[kani::proof]#[kani::unwind(129)]#[kani::stub_verified(havoc_bytes)]fn havoc_nonconstant_control(){
 let mut data=vec![0u8;58295];let a:&mut[u8;58295]=data.as_mut_slice().try_into().unwrap();havoc_bytes(a);
 let k:usize=kani::any();kani::assume(k<58295);
 assert_eq!(data[k],0,"NLM arbitrary prestate initializer must permit nonzero bytes");
}
fn view<const WRONG:bool>() {
 let n:usize=kani::any();kani::assume(n<=58295);
 let mut bytes=vec![0u8;58295];let a:&mut[u8;58295]=bytes.as_mut_slice().try_into().unwrap();havoc_bytes(a);bytes.truncate(n);let k:usize=kani::any();
 let original=bytes.as_ptr();
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let declared=if kani::any(){Ok(kani::any::<usize>())}else{Err(ProgramError::Custom(kani::any()))};
 let a=OwnedAccount{key,owner,is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:declared,bytes:Ok(bytes)};
 let exact=match a.data(){Ok(slice)=>slice.len()==n&&slice.as_ptr()==original,Err(_)=>false};
 assert!(exact!=WRONG,"NLM owned getter metadata on an arbitrary byte prestate");
}
fn byte_alias<const WRONG:bool>() {
 let mut bytes=vec![0u8;58295];let a:&mut[u8;58295]=bytes.as_mut_slice().try_into().unwrap();havoc_bytes(a);
 let k:usize=kani::any();kani::assume(k<58295);let before=bytes[k];
 let key=Pubkey::new_from_array([0;32]);
 let a=OwnedAccount{key,owner:key,is_signer:false,is_writable:false,executable:false,length:Ok(58295),bytes:Ok(bytes)};
 assert!((a.data().unwrap()[k]==before)!=WRONG,"NLM actual getter preserves arbitrary byte at exact proof-account extent");
}
fn deferred<const WRONG:bool>() {
 let value:u8=kani::any();let mut data=[value];let mut lamports:u64=kani::any();
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();
 let a=AccountInfo::new(&key,signer,writable,&mut lamports,&mut data,&owner,executable,0);
 let out=snapshot(&a,58295,58295);
 let exact=out.length==Ok(1)&&matches!(out.bytes,Err(ProgramError::InvalidAccountData))&&out.key==key&&out.owner==owner&&out.is_signer==signer&&out.is_writable==writable&&out.executable==executable&&a.try_borrow_mut_data().is_ok();
 assert!(exact!=WRONG,"NLM snapshot rejected length restores guard and retains all metadata");
}
fn conflict<const WRONG:bool>() {
 let value:u8=kani::any();let mut data=[value];let mut lamports=0;
 let key=Pubkey::new_from_array([0;32]);
 let a=AccountInfo::new(&key,false,false,&mut lamports,&mut data,&key,false,0);
 let held=a.try_borrow_mut_data().unwrap();let out=snapshot(&a,1,1);
 let exact=out.length==Err(ProgramError::AccountBorrowFailed)&&matches!(out.bytes,Err(ProgramError::AccountBorrowFailed))&&a.try_borrow_data().is_err();
 assert!(exact!=WRONG,"NLM snapshot exact deferred borrow error preserves external live token");
 drop(held);assert!(a.try_borrow_mut_data().is_ok());
}
fn copied<const WRONG:bool>() {
 let src:[u8;1]=kani::any();let mut dst:[u8;2]=kani::any();let before=dst[1];let original=src[0];
 unsafe{KMX_copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),1);}
 let exact=dst[0]==original&&dst[1]==before&&src[0]==original;
 assert!(exact!=WRONG,"NLM exact KMX one-byte iteration and disjoint observer, all local prestate bytes arbitrary");
}
fn end(length:usize,proof_length:usize)->Result<usize,ProgramError>{
 let proof_start:usize=688;
 let proof_end=proof_start.checked_add(proof_length).ok_or(ProgramError::InvalidAccountData)?;
 if length!=proof_end{return Err(ProgramError::InvalidAccountData);}
 Ok(proof_end)
}
fn end_check<const WRONG:bool>(){
 let length:usize=kani::any();let proof_length:usize=kani::any();let out=end(length,proof_length);
 let sum=688u128+(proof_length as u128);
 let expected=if sum>(usize::MAX as u128)||(length as u128)!=sum{Err(ProgramError::InvalidAccountData)}else{Ok(sum as usize)};
 assert!((out==expected)!=WRONG,"NLM owned checked-end rejects overflow and unequal actual length");
}
fn data_errors<const WRONG:bool>(){
 let e=if kani::any(){ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData};
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let declared=if kani::any(){Ok(kani::any::<usize>())}else{Err(ProgramError::Custom(kani::any()))};
 let a=OwnedAccount{key,owner,is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:declared,bytes:Err(e.clone())};
 let exact=a.data()==Err(e);
 assert!(exact!=WRONG,"NLM owned data complete actual snapshot error clone reply");
}
fn length_reply<const WRONG:bool>(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let length=if kani::any(){Ok(kani::any::<usize>())}else{Err(ProgramError::AccountBorrowFailed)};
 let a=OwnedAccount{key,owner,is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:length.clone(),bytes:Err(ProgramError::InvalidAccountData)};
 assert!((a.data_len()==length)!=WRONG,"NLM owned length exact scalar and borrow-error clone");
}
macro_rules! proof {($name:ident,$f:ident,$wrong:expr)=>{
 #[kani::proof]#[kani::unwind(129)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
 fn $name(){$f::<$wrong>()}
}}
macro_rules! proof_seed {($name:ident,$f:ident,$wrong:expr)=>{
 #[kani::proof]#[kani::unwind(129)]#[kani::stub_verified(havoc_bytes)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
 fn $name(){$f::<$wrong>()}
}}
proof_seed!(havoc_frame_pass,havoc_frame,false);proof_seed!(havoc_frame_control,havoc_frame,true);
proof_seed!(owned_byte,byte_alias,false);proof_seed!(owned_byte_control,byte_alias,true);
proof_seed!(owned_view,view,false);proof_seed!(owned_view_control,view,true);
proof!(snapshot_deferred,deferred,false);proof!(snapshot_deferred_control,deferred,true);
proof!(snapshot_conflict,conflict,false);proof!(snapshot_conflict_control,conflict,true);
proof!(copy_window,copied,false);proof!(copy_window_control,copied,true);
proof!(owned_end,end_check,false);proof!(owned_end_control,end_check,true);
proof!(owned_data_errors,data_errors,false);proof!(owned_data_errors_control,data_errors,true);
proof!(owned_length,length_reply,false);proof!(owned_length_control,length_reply,true);
'''
P='programs/r1-cost-probe/src/';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
patch=''
for n in ['lib.rs','r1_pool_adapter_owned.rs']:
 before=subprocess.check_output(['git','show',rev+':'+P+n],text=True)
 after='#![cfg_attr(kani,feature(allocator_api))]\n'+before if n=='lib.rs' else before+'\n#[cfg(kani)]\n#[path="NLM_native.rs"]\nmod NLM_native;\n'
 patch+='diff --git a/'+P+n+' b/'+P+n+'\n'+''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+P+n,tofile='b/'+P+n))
n=P+'NLM_native.rs';patch+='diff --git a/'+n+' b/'+n+'\nnew file mode 100644\n'+''.join(difflib.unified_diff([],text.splitlines(True),fromfile='/dev/null',tofile='b/'+n))
(E/'NLM_native.patch').write_text(patch)
