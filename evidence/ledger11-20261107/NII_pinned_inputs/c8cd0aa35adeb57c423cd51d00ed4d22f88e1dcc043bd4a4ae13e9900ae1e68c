from pathlib import Path
import json
from NGL_prepare import update,P,E
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text())
# Controls are distinct false properties in the identical build configuration.
for n in ['NGL_entry.rs','NGL_adapter.rs','NGL_owned.rs']:
 s=I[P+n]
 import re
 names=re.findall(r'\nfn (\w+)\(',s)
 # Only proof functions, not support constructors.
 for name in names:
  if name in ['account']:continue
  begin=s.index('#[kani::proof]', max(0,s.index('fn '+name)-250)) if False else 0
 # Copy each annotated proof block, preserving body except the final expected verdict.
 blocks=re.findall(r'(#\[kani::proof\][\s\S]*?\nfn (\w+)\([^\n]*\{[^\n]*\}\n)',s)
 for block,name in blocks:
  wrong=block.replace('fn '+name+'(', 'fn '+name+'_wrong(').replace(' != cfg!(NGL_invert)',' == cfg!(NGL_invert)')
  assert wrong!=block;s+='\n'+wrong
 I[P+n]=s
s=I[P+'NGL_owned.rs'];attrs='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
for name,body in [
 ('length_deferred','let mut a=core::mem::ManuallyDrop::new(account());let n:usize=kani::any();let tag:u8=kani::any();kani::assume(tag<3);a.length=if tag==0{Ok(n)}else if tag==1{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)};let r=a.data_len();let exact=match tag{0=>matches!(r,Ok(v)if v==n),1=>matches!(r,Err(ProgramError::AccountBorrowFailed)),_=>matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact != cfg!(NGL_invert));'),
 ('data_deferred','let mut a=core::mem::ManuallyDrop::new(account());let borrow:bool=kani::any();a.bytes=Err(if borrow{ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData});let r=a.data();let exact=if borrow{matches!(r,Err(ProgramError::AccountBorrowFailed))}else{matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact != cfg!(NGL_invert));'),
 ('checkpoint_meta','let owner:[u8;32]=kani::any();let program:[u8;32]=kani::any();let mut a=core::mem::ManuallyDrop::new(account());a.owner=Pubkey::new_from_array(owner);let writable:bool=kani::any();let n:usize=kani::any();let error:bool=kani::any();a.length=if error{Err(ProgramError::AccountBorrowFailed)}else{Ok(n)};let invalid=owner!=program||a.is_signer||a.executable||a.is_writable!=writable;let r=require_verifier_checkpoint(&a,&Pubkey::new_from_array(program),writable);let exact=if invalid{matches!(r,Err(ProgramError::InvalidAccountData))}else if error{matches!(r,Err(ProgramError::AccountBorrowFailed))}else if n!=1768{matches!(r,Err(ProgramError::InvalidAccountData))}else{matches!(r,Ok(()))};assert!(exact != cfg!(NGL_invert));')]:
 s+='\n'+attrs+'fn '+name+'(){'+body+'}\n'+attrs+'fn '+name+'_wrong(){'+body.replace(' != cfg!(NGL_invert)',' == cfg!(NGL_invert)')+'}\n'
I[P+'NGL_owned.rs']=s
update({n:s for n,s in I.items() if n.startswith(P)},'stage1_helpers')
queue=[]
for i,t in enumerate(['NGL_entry::rejected_entry2_wrong','r1_pool_adapter::NGL_adapter::readonly_meta','r1_pool_adapter::NGL_adapter::readonly_meta_wrong','r1_pool_adapter::NGL_adapter::key_copy','r1_pool_adapter::NGL_adapter::key_copy_wrong','r1_pool_adapter::owned::NGL_owned::readonly_account','r1_pool_adapter::owned::NGL_owned::readonly_account_wrong','r1_pool_adapter::owned::NGL_owned::length_deferred','r1_pool_adapter::owned::NGL_owned::length_deferred_wrong','r1_pool_adapter::owned::NGL_owned::data_deferred','r1_pool_adapter::owned::NGL_owned::data_deferred_wrong','r1_pool_adapter::owned::NGL_owned::checkpoint_meta','r1_pool_adapter::owned::NGL_owned::checkpoint_meta_wrong'],2):
 queue.append(dict(attempt=f'NGL_K{i:03}',kind='kani',target=t,expected=1 if t.endswith('_wrong') else 0))
(E/'NGL_STAGE1_QUEUE.json').write_text(json.dumps(queue,indent=1)+'\n')
