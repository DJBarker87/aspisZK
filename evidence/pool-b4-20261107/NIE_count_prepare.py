from pathlib import Path
import sys
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_native_prepare import stage,attrs

def prepare(control):
 assert control in ['none','reply','frame']
 mutation={'none':'','reply':'reply=Err(ProgramError::InvalidAccountData);','frame':'account.is_signer=!account.is_signer;'}[control]
 src='''use super::*;
ATTR
#[kani::proof]
#[kani::unwind(33)]
fn association() {
 let mut data:[u8;3]=kani::any();let before=data;let mut balance:u64=kani::any();let old=balance;
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let sign:bool=kani::any();
 let mut account=AccountInfo::new(&key,sign,kani::any(),&mut balance,&mut data,&owner,kani::any(),kani::any());let alias=account.clone();
 let accounts=[account.clone(),alias.clone()];let len:usize=kani::any();kani::assume(len<=2);let expected:usize=kani::any();
 let guard=alias.try_borrow_mut_data().unwrap();
 let mut reply=require_exact_account_count(&accounts[..len],expected);
 drop(guard);
 MUTATION
 let correct=if len==expected {Ok(())}else if len<expected {Err(ProgramError::NotEnoughAccountKeys)}else{Err(ProgramError::InvalidArgument)};
 assert!(reply==correct);assert!(account.is_signer==sign);assert!(account.data.try_borrow_mut().is_ok());assert!(alias.lamports()==old);
 let q:usize=kani::any();kani::assume(q<3);assert!(alias.try_borrow_data().unwrap()[q]==before[q]);
}
'''.replace('ATTR',attrs()).replace('MUTATION',mutation)
 stage('programs/aspis-pool/src/pair_forest.rs',src,'actual exact-count helper on aliased live-exclusive carrier, arbitrary expected usize and frame','positive' if control=='none' else 'negative','Every expected usize, logical list length0..2, arbitrary AccountInfo metadata/key/owner/lamports/data on aliased physical cells with a valid existing exclusive data guard; helper reads only list length.','All production list cardinalities/physical layout and parent count PacketDomains remain OPEN; bounded physical list is not a production restriction.',dict(control=control,reused_model='NHC_NGG_Count.result'))
