from NMM_native import *
from NMM_registry_native import common
P='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
HELP='''
use core::cell::UnsafeCell;
#[repr(C)]
struct NMM_Account {account:OwnedAccount,record:UnsafeCell<Option<(*const OwnedAccount,u32)>>}
fn NMM_cell(a:&OwnedAccount)->&UnsafeCell<Option<(*const OwnedAccount,u32)>>{
 unsafe{&*((a as *const OwnedAccount as *const u8).add(core::mem::offset_of!(NMM_Account,record)) as *const UnsafeCell<Option<(*const OwnedAccount,u32)>>)}
}
fn NMM_data_cut(a:&OwnedAccount)->Result<&[u8],ProgramError>{
 let word:u32=kani::any();let log=NMM_cell(a);
 unsafe{assert!((*log.get()).is_none(),"one data call per account");log.get().write(Some((a as *const OwnedAccount,word)));}
 Err(ProgramError::Custom(word))
}
fn NMM_replay_data(a:&OwnedAccount)->Result<&[u8],ProgramError>{
 let record=unsafe{(*NMM_cell(a).get()).take()};
 assert!(record.is_some(),"recorded exact data call present");
 match record {Some((ptr,word))=>{assert!(ptr==a as *const OwnedAccount,"exact child account argument");Err(ProgramError::Custom(word))},None=>Err(ProgramError::InvalidArgument)}
}
fn NMM_account<const N:usize>()->NMM_Account{
 let image:[u8;N]=kani::any();let bytes:Box<[u8]>=Box::new(image);let bytes=bytes.into_vec();
 NMM_Account{account:OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(N),bytes:Ok(bytes)},record:UnsafeCell::new(None)}
}
'''
ANN='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(super::OwnedAccount::data,NMM_data_cut)]
'''
def attempt(a,version,mode):
 borrowed=str(version).endswith("borrow");version=int(str(version).removesuffix("borrow"));R,T=(128,192) if version==1 else (256,320)
 ref=(E/'NMM_FROZEN_234.rs').read_text().replace('fn authenticate_invariant_release_registry(','fn NMM_reference(',1)
 for account in ['registry_account','entry_account']:ref=ref.replace(account+'.data()', 'NMM_replay_data('+account+')')
 text=common()+HELP+ref+ANN+'''fn stage(){
 let master=any_master();let ma=NMM_account::<1>();let reg=NMM_account::<RS>();let ent=NMM_account::<ES>();
 let verifier=Pubkey::new_from_array(kani::any());let pool=Pubkey::new_from_array(kani::any());let slot:u64=kani::any();
 kani::assume((master.verifier_policy.flags&POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT!=0)==V2);
 let observer:usize=kani::any();kani::assume(observer<RS);let before=reg.account.bytes.as_ref().unwrap()[observer];
 let native=authenticate_invariant_release_registry(&verifier,&pool,&ma.account,&master,&reg.account,&ent.account,slot);
 let reference=NMM_reference(&verifier,&pool,&ma.account,&master,&reg.account,&ent.account,slot);
 assert!(native==reference,"complete registry outcome on recorded data error reply");
 assert!(reg.account.bytes.as_ref().unwrap()[observer]==before,"immutable full data frame");
 unsafe {assert!((*reg.record.get()).is_none()&&(*ent.record.get()).is_none(),"no unmatched data call");}
}
'''.replace('RS',str(R)).replace('ES',str(T)).replace('V2','true' if version==2 else 'false')
 if borrowed:
  text=text.replace('Option<(*const OwnedAccount,u32)>','Option<(*const OwnedAccount,ProgramError)>')
  text=text.replace('let word:u32=kani::any();let log=NMM_cell(a);','let word=if kani::any(){ProgramError::AccountBorrowFailed}else{ProgramError::Custom(kani::any())};let log=NMM_cell(a);')
  text=text.replace('a as *const OwnedAccount,word)))','a as *const OwnedAccount,word.clone())))')
  text=text.replace('Err(ProgramError::Custom(word))','Err(word)')
  text=text.replace('fn NMM_account<const N:usize>()->NMM_Account','fn NMM_account<const N:usize>(bad:bool)->NMM_Account')
  text=text.replace('length:Ok(N),bytes:Ok(bytes)', 'length:if bad{Err(ProgramError::AccountBorrowFailed)}else{Ok(N)},bytes:if bad{Err(ProgramError::AccountBorrowFailed)}else{Ok(bytes)}')
  text=text.replace('NMM_account::<1>()','NMM_account::<304>(false)')
  for extent in [R,T]:text=text.replace('NMM_account::<'+str(extent)+'>()','NMM_account::<'+str(extent)+'>(true)')
  text=text.replace('let before=reg.account.bytes.as_ref().unwrap()[observer];','let before=reg.account.bytes.clone();')
  text=text.replace('reg.account.bytes.as_ref().unwrap()[observer]==before','reg.account.bytes==before')
  if mode=='reply':text=text.replace('Err(word)},None','Err(ProgramError::InvalidArgument)},None')
 if mode=='reply':text=text.replace('Err(ProgramError::Custom(word))},None','Err(ProgramError::Custom(word^1))},None')
 if mode=='argument':text=text.replace('&master,&reg.account,&ent.account,slot);','&master,&ent.account,&reg.account,slot);',1)
 if mode=='footprint':text=text.replace('log.get().write(Some((a as *const OwnedAccount,word)));','log.get().write(None);')
 if mode=='copy':text=text.replace('assert!(native==reference,','let src:[u32;8]=kani::any();let mut dst=[0u32;8];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),8)};assert!(dst!=src,')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/NMM_bl_registry.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::owned::NMM_bl_registry::stage',P,'NMM_bl_registry',text,mode)
if __name__=='__main__':
 import sys
 r=attempt(*sys.argv[1:]);sys.exit(r['exit_status'])
