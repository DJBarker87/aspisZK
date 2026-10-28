from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent
files={}
lib='programs/r1-cost-probe/src/lib.rs'
files[lib]='''
#[cfg(kani)]
mod NCK_kmx { extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }
#[cfg(kani)]
mod NCK_dispatch {
 use super::*;
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn admitted_exact(){
  let data:[u8;8]=kani::any();let n:usize=kani::any();kani::assume(n<=8);
  let expected=(n==2 && data[0]==3 && (data[1]==10 || data[1]==11)) ||
   (n>=4 && data[0]==65 && data[1]==83 && data[2]==81 && data[3]==56);
  assert_eq!(pool_route::admitted(&data[..n]),expected);
 }
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn admitted_wrong(){assert!(!pool_route::admitted(b"ASQ8"));}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn entry_reject(){
  let data:[u8;8]=kani::any();let n:usize=kani::any();kani::assume(n<=8);
  kani::assume(!pool_route::admitted(&data[..n]));
  assert_eq!(process_r1_cost_probe_instruction(&Pubkey::new_from_array(kani::any()),&[],&data[..n]),Err(ProgramError::InvalidInstructionData));
 }
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn entry_wrong(){assert!(process_r1_cost_probe_instruction(&Pubkey::new_from_array([0;32]),&[],b"no").is_ok());}
}
'''
files['programs/r1-cost-probe/src/r1_pool_adapter.rs']='''
#[cfg(kani)]
mod NCK_meta {
 use super::*;
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn buffer_exact(){let s:bool=kani::any();let w:bool=kani::any();let e:bool=kani::any();assert_eq!(readonly_buffer_meta_ok(s,w,e),if s||w||e{Err(ProgramError::InvalidAccountData)}else{Ok(())});}
 #[kani::proof] fn buffer_wrong(){assert!(readonly_buffer_meta_ok(true,false,false).is_ok());}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn account_exact(){let a:[u8;32]=kani::any();let b:[u8;32]=kani::any();let s:bool=kani::any();let w:bool=kani::any();let e:bool=kani::any();let actual=readonly_meta_ok(&Pubkey::new_from_array(a),&Pubkey::new_from_array(b),s,w,e);let expected=if a!=b||s||w||e{Err(ProgramError::InvalidAccountData)}else{Ok(())};assert_eq!(actual,expected);}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn account_wrong(){assert!(readonly_meta_ok(&Pubkey::new_from_array([0;32]),&Pubkey::new_from_array([1;32]),false,false,false).is_ok());}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn pool_id(){assert_eq!(pool_program_id(),AUDIT_POOL_PROGRAM);}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn registry_id(){assert_eq!(registry_program_id(),AUDIT_REGISTRY_PROGRAM);}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn pool_wrong(){assert_ne!(pool_program_id(),AUDIT_POOL_PROGRAM);}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn registry_wrong(){assert_ne!(registry_program_id(),AUDIT_REGISTRY_PROGRAM);}
}
'''
files['programs/r1-cost-probe/src/r1_pool_adapter_owned.rs']='''
#[cfg(kani)]
mod NCK_owned {
 use super::*;
 fn account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Err(ProgramError::Custom(kani::any()))}}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn key(){let a=account();assert!(core::ptr::eq(a.key(),&a.key));}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn key_wrong(){let a=account();assert!(!core::ptr::eq(a.key(),&a.key));}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn owner(){let a=account();assert!(core::ptr::eq(a.owner(),&a.owner));}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn owner_wrong(){let a=account();assert!(!core::ptr::eq(a.owner(),&a.owner));}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn data_error(){let a=account();assert_eq!(a.data(),a.bytes.as_ref().map(|x|x.as_slice()).map_err(|e|e.clone()));}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn data_error_wrong(){let a=account();assert!(a.data().is_ok());}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn length_ok(){let a=account();assert_eq!(a.data_len(),a.length);}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn length_wrong(){let a=account();assert!(a.data_len().is_err());}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn readonly_buffer(){let a=account();assert_eq!(require_readonly_buffer(&a),if a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())});}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn readonly_buffer_wrong(){let mut a=account();a.executable=true;assert!(require_readonly_buffer(&a).is_ok());}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn checkpoint_meta(){let a=account();let p=Pubkey::new_from_array(kani::any());let w:bool=kani::any();let expected=if a.owner!=p||a.is_signer||a.executable||a.is_writable!=w||a.length!=Ok(1768){Err(ProgramError::InvalidAccountData)}else{Ok(())};assert_eq!(require_verifier_checkpoint(&a,&p,w),expected);}
 #[kani::proof] #[kani::unwind(36)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn checkpoint_wrong(){let mut a=account();a.is_signer=true;assert!(require_verifier_checkpoint(&a,&a.owner,false).is_ok());}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn stage2_empty(){let p=Pubkey::new_from_array(kani::any());let d:[u8;8]=kani::any();assert_eq!(stage2(&p,&[],&d),Err(ProgramError::InvalidInstructionData));}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn stage2_empty_wrong(){let p=Pubkey::new_from_array([0;32]);assert!(stage2(&p,&[],b"ASQ8").is_ok());}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn stage2_owned_empty(){let p=Pubkey::new_from_array(kani::any());let d:[u8;8]=kani::any();let slot:Result<u64,ProgramError>=if kani::any(){Ok(kani::any())}else{Err(ProgramError::Custom(kani::any()))};assert_eq!(stage2_owned(&p,&[],&d,slot),Err(ProgramError::InvalidInstructionData));}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn stage2_owned_empty_wrong(){assert!(stage2_owned(&Pubkey::new_from_array([0;32]),&[],b"ASQ8",Ok(0)).is_ok());}
}
'''
patch=''
for n,append in files.items():
 old=subprocess.check_output(['git','show','4bb3b3f5:'+n],text=True)
 new=('#![cfg_attr(kani, feature(allocator_api))]\n' if n==lib else '')+old+append
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NCK_native.patch').write_text(patch)
