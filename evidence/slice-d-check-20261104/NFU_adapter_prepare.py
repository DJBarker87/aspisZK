from pathlib import Path
import subprocess,json
from NFU_add_inputs import update
E=Path(__file__).resolve().parent
C='programs/r1-cost-probe/src/';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
base=subprocess.check_output(['git','show',F+':'+C+'r1_pool_adapter_owned.rs'],text=True)
code='''use super::*;
fn account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::proof]
fn readonly_buffer(){let a=account();let r=require_readonly_buffer(&a);let expected=if a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};assert!((r==expected) != cfg!(NFU_invert));}
#[kani::proof]
fn key_identity(){let a=account();assert!((core::ptr::eq(a.key(),&a.key)) != cfg!(NFU_invert));}
#[kani::proof]
fn owner_identity(){let a=account();assert!((core::ptr::eq(a.owner(),&a.owner)) != cfg!(NFU_invert));}
'''
update({C+'r1_pool_adapter_owned.rs':base+'\n#[cfg(kani)]\n#[path="NFU_owned.rs"]\nmod NFU_owned;\n',C+'NFU_owned.rs':code},'NFU_adapter')
