from pathlib import Path
import sys
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_native_prepare import stage,attrs

def prepare(case,negative):
 assert case in range(3)
 setting=['kani::assume(key!=expected);','expected=key;kani::assume(exec || sign || !write);','expected=key;exec=false;sign=false;write=true;owner=solana_sdk_ids::system_program::id();kani::assume(program!=owner);'][case]
 expectation='let ok=len==0;assert!(matches!(reply,Ok(FreshPdaPreparationV1::CreateOrAllocateSystemOwned))==ok);if !ok {assert!(reply==Err(ProgramError::Custom(PoolV1ProgramError::InvalidFreshAccount as u32)));}' if case==2 else 'assert!(reply==Err(ProgramError::Custom(PoolV1ProgramError::InvalidFreshAccount as u32)));'
 src='''use super::*;
ATTR
#[kani::proof]
#[kani::unwind(33)]
fn association() {
 let mut bytes:[u8;3]=kani::any();let before=bytes;let mut balance:u64=kani::any();let old=balance;
 let key=Pubkey::new_from_array(kani::any());let mut expected=Pubkey::new_from_array(kani::any());let program=Pubkey::new_from_array(kani::any());let mut owner=Pubkey::new_from_array(kani::any());
 let mut exec:bool=kani::any();let mut sign:bool=kani::any();let mut write:bool=kani::any();
 SETTING
 let len:usize=kani::any();kani::assume(len<=3);let exact_bytes:usize=kani::any();
 let account=AccountInfo::new(&key,sign,write,&mut balance,&mut bytes[..len],&owner,exec,kani::any());let alias=account.clone();
 let shared=if kani::any(){Some(alias.try_borrow_data().unwrap())}else{None};
 let reply=plan_fresh_program_pda(&account,&program,&expected,exact_bytes);
 EXPECTATION
 drop(shared);
 NEGATIVE
 assert!(alias.try_borrow_mut_data().is_ok());assert!(alias.lamports()==old);
 if len>0 {let q:usize=kani::any();kani::assume(q<len);assert!(alias.try_borrow_data().unwrap()[q]==before[q]);}
}
'''.replace('ATTR',attrs()).replace('SETTING',setting).replace('EXPECTATION',expectation).replace('NEGATIVE','let leaked=alias.try_borrow_data().unwrap();core::mem::forget(leaked);' if negative else '')
 stage('programs/aspis-pool/src/processor.rs',src,'actual fresh-PDA planning caller branch '+str(case)+' alias cleanup/frame','negative' if negative else 'positive','Arbitrary keys/flags/exact_bytes/lamports/rent, logical0..3 arbitrary bytes and optional existing shared alias; exact address/privilege-rejection or System branch; Pool distinct from System. No exclusive accessor input constructed.','Production parent-to-accessor borrowability and full program-owned zero-scan/whole physical domain remain OPEN.',dict(case=case))
