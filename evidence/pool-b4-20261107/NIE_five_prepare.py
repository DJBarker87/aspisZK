from pathlib import Path
import sys
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_native_prepare import stage,attrs

def prepare(large,negative):
 src='''use super::*;
ATTR
#[kani::proof]
#[kani::unwind(289)]
fn association() {
 assert!(core::mem::size_of::<AccountInfo>()==48);
 let mut data:[u8;3]=kani::any();let before=data;let mut balance:u64=kani::any();let old=balance;
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let base=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),kani::any());
 let accounts=[base.clone(),base.clone(),base.clone(),base.clone(),base.clone(),base.clone()];
 let len:usize=LENGTH;
 let shared=base.try_borrow_data().unwrap();
 let got=exact_five_withdrawal_accounts(&accounts[..len]);
 assert!(matches!(got,Err(ref e) if *e==ERROR));drop(got);drop(shared);
 NEGATIVE
 assert!(base.try_borrow_mut_data().is_ok());assert!(base.lamports()==old);let q:usize=kani::any();kani::assume(q<3);assert!(base.try_borrow_data().unwrap()[q]==before[q]);
}
'''.replace('ATTR',attrs()).replace('LENGTH','6' if large else '{let n:usize=kani::any();kani::assume(n<5);n}').replace('ERROR','ProgramError::InvalidArgument' if large else 'ProgramError::NotEnoughAccountKeys').replace('NEGATIVE','let leaked=base.try_borrow_data().unwrap();core::mem::forget(leaked);' if negative else '')
 stage('programs/aspis-pool/src/vault.rs',src,'actual withdrawal physical-list arity rejection + source borrow/frame','negative' if negative else 'positive','Every list length0..4 or6 in the selected cut, valid AccountInfo metadata and true data/lamport aliases, existing shared guard, arbitrary3 bytes and lamports. Arity rejects before uniqueness loop; no whole-buffer loop is run.','Admitted five-account uniqueness/selection and same-request custody/CPI frames remain OPEN.',dict(large=large))
