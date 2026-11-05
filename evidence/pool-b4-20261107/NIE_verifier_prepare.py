from pathlib import Path
import sys
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_native_prepare import stage,attrs

def prepare(control):
 assert control in ['none','reply','flag','borrow','rc','identity']
 mutation={'none':'','reply':'reply=if reply.is_ok(){Err(ProgramError::InvalidArgument)}else{Ok(())};','flag':'account.is_signer = !account.is_signer;','borrow':'let leaked=alias.try_borrow_data().unwrap();core::mem::forget(leaked);','rc':'let leaked=account.clone();core::mem::forget(leaked);','identity':'account.data=alloc::rc::Rc::new(core::cell::RefCell::new(&mut other[..]));'}[control]
 src='''use super::*;
use alloc::rc::Rc;
ATTR
#[kani::proof]
#[kani::unwind(33)]
fn association() {
 let mut bytes:[u8;3]=kani::any();let before=bytes;let mut other:[u8;3]=kani::any();
 let mut balance:u64=kani::any();let old=balance;
 let key=Pubkey::new_from_array(kani::any());let selected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let exec:bool=kani::any();let sign:bool=kani::any();let write:bool=kani::any();
 let rent:u64=kani::any();
 let mut account=AccountInfo::new(&key,sign,write,&mut balance,&mut bytes,&owner,exec,rent);let alias=account.clone();
 let data_mode:u8=kani::any();kani::assume(data_mode<=2);let lamp_mode:u8=kani::any();kani::assume(lamp_mode<=2);
 let d_shared=if data_mode==1{Some(alias.try_borrow_data().unwrap())}else{None};
 let d_exclusive=if data_mode==2{Some(alias.try_borrow_mut_data().unwrap())}else{None};
 let l_shared=if lamp_mode==1{Some(alias.try_borrow_lamports().unwrap())}else{None};
 let l_exclusive=if lamp_mode==2{Some(alias.try_borrow_mut_lamports().unwrap())}else{None};
 let dc=Rc::strong_count(&account.data);let lc=Rc::strong_count(&account.lamports);
 let expected=key==selected && exec && !sign && !write && (owner==bpf_loader::id() || owner==bpf_loader_upgradeable::id() || owner==loader_v4::id());
 let mut reply=require_verifier_program(&account,&selected);
 drop(d_shared);drop(d_exclusive);drop(l_shared);drop(l_exclusive);
 MUTATION
 assert!(reply.is_ok()==expected);
 assert!(matches!(reply,Ok(())) || reply==Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into()));
 assert!(account.is_signer==sign && account.is_writable==write && account.executable==exec && account.key==&key && account.owner==&owner && account.rent_epoch==rent);
 assert!(Rc::ptr_eq(&account.data,&alias.data) && Rc::ptr_eq(&account.lamports,&alias.lamports));
 assert!(Rc::strong_count(&account.data)==dc && Rc::strong_count(&account.lamports)==lc);
 assert!(alias.try_borrow_mut_data().is_ok() && alias.try_borrow_mut_lamports().is_ok());
 assert!(alias.lamports()==old);let q:usize=kani::any();kani::assume(q<3);assert!(alias.try_borrow_data().unwrap()[q]==before[q]);
}
'''.replace('ATTR',attrs()).replace('MUTATION',mutation)
 stage('programs/aspis-pool/src/pair_forest_dispatch.rs',src,'actual selected verifier metadata caller: nine live-guard combinations, Rc identity/count and byte/balance frames','positive' if control=='none' else 'negative','Arbitrary keys/selected/owner/flags/lamports/rent and3 arbitrary bytes; true Rc aliases with independently selected none/shared/exclusive data and lamport guards. This helper reads no data/lamport accessor.','Authenticated registry selection, same-state seven metas and physical production list/entry domains remain OPEN; loader law reused from CLOSED NHC supported_loader.',dict(control=control))
