"""Actual creation-helper rejected prefixes with explicit local CPI unreachability."""
from pathlib import Path
import sys
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_native_prepare import stage,attrs

def prepare(function,case,negative):
 assert function in ['create_or_allocate_pda_with_rent','create_or_allocate_with_seed_with_rent'] and case in range(3)
 setting=[
  'kani::assume(!payer_sign || !payer_write || payer_exec || payer_owner!=system_id);',
  'payer_sign=true;payer_write=true;payer_exec=false;payer_owner=system_id;kani::assume(system_key!=system_id || system_owner!=native_id || !system_exec || system_sign || system_write);',
  'payer_sign=true;payer_write=true;payer_exec=false;payer_owner=system_id;system_key=system_id;system_owner=native_id;system_exec=true;system_sign=false;system_write=false;kani::assume(account_owner!=system_id);'
 ][case]
 call='create_or_allocate_pda_with_rent(&mut runtime,&payer,&account,&system,exact_bytes,&program,&[],&Rent::default())' if function=='create_or_allocate_pda_with_rent' else 'create_or_allocate_with_seed_with_rent(&mut runtime,&payer,&account,&payer,"",&system,exact_bytes,&program,&[],&Rent::default())'
 error=['InvalidPayer','InvalidSystemProgram','InvalidFreshAccount'][case]
 src='''use super::*;
struct RuntimeLog {calls:usize}
impl PoolCpiRuntimeV1 for RuntimeLog {
 fn invoke<'i>(&mut self,_:&Instruction,_:&[AccountInfo<'i>])->ProgramResult {self.calls+=1;assert!(false);Ok(())}
 fn invoke_signed<'i>(&mut self,_:&Instruction,_:&[AccountInfo<'i>],_:&[&[&[u8]]])->ProgramResult {self.calls+=1;assert!(false);Ok(())}
}
ATTR
#[kani::proof]
#[kani::unwind(33)]
fn association() {
 let mut bytes:[u8;3]=kani::any();let before=bytes;
 let mut balance:u64=kani::any();let old_balance=balance;
 let program=Pubkey::new_from_array(kani::any());let payer_key=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let mut payer_owner=Pubkey::new_from_array(kani::any());let account_owner=Pubkey::new_from_array(kani::any());
 let mut system_key=Pubkey::new_from_array(kani::any());let mut system_owner=Pubkey::new_from_array(kani::any());
 let system_id=system_program::id();let native_id=native_loader::id();
 let mut payer_sign:bool=kani::any();let mut payer_write:bool=kani::any();let mut payer_exec:bool=kani::any();
 let mut system_sign:bool=kani::any();let mut system_write:bool=kani::any();let mut system_exec:bool=kani::any();
 SETTING
 let base=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut bytes,&account_owner,kani::any(),kani::any());
 let payer=AccountInfo {key:&payer_key,owner:&payer_owner,is_signer:payer_sign,is_writable:payer_write,executable:payer_exec,..base.clone()};
 let system=AccountInfo {key:&system_key,owner:&system_owner,is_signer:system_sign,is_writable:system_write,executable:system_exec,..base.clone()};
 let account=base.clone();
 let shared=base.try_borrow_data().unwrap();
 let mut runtime=RuntimeLog{calls:0};let exact_bytes:usize=kani::any();
 let reply=CALL;
 assert!(reply==Err(ProgramError::Custom(PoolV1ProgramError::ERROR as u32)));
 drop(shared);
 NEGATIVE
 assert!(runtime.calls==0);
 assert!(base.try_borrow_mut_data().is_ok());
 assert!(base.lamports()==old_balance);
 let q:usize=kani::any();kani::assume(q<3);assert!(base.try_borrow_data().unwrap()[q]==before[q]);
}
'''.replace('ATTR',attrs()).replace('SETTING',setting).replace('CALL',call).replace('ERROR',error).replace('NEGATIVE','runtime.calls=1;' if negative else '')
 stage('programs/aspis-pool/src/processor.rs',src,'actual '+function+' pre-accessor rejected prefix '+str(case)+'; local CPI unreachability and aliased frame','negative' if negative else 'positive','Arbitrary keys/metadata/lamports/exact_bytes; three-byte shared physical data and lamport cells across valid AccountInfo aliases; stated payer/system/foreign-account-owner rejection branch; existing shared guard only. No accessor conflict or transaction input is constructed.','Returning creation/System CPI, accepted account borrowability and all production root/alias/caller domains remain OPEN. The runtime implementation is an unreachability checker on these rejected prefixes, not an assumed successful CPI.',dict(function=function,case=case,control='corrupt local CPI-count poststate' if negative else None))
if __name__=='__main__':prepare(sys.argv[1],int(sys.argv[2]),sys.argv[3]=='negative')
