from NGL_prepare import update,E,P
import json
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'NGL_owned.rs'];s+='''
fn length_observation(r:Result<usize,ProgramError>)->[usize;2]{match r{Ok(n)=>[0,n],Err(ProgramError::AccountBorrowFailed)=>[1,0],Err(ProgramError::InvalidAccountData)=>[2,0],Err(_)=>[3,0]}}
fn length_observation_ref(a:&OwnedAccount)->[usize;2]{match a.length{Ok(n)=>[0,n],Err(ProgramError::AccountBorrowFailed)=>[1,0],Err(ProgramError::InvalidAccountData)=>[2,0],_=>[3,0]}}
#[kani::requires(length_domain(&a.length))]
#[kani::ensures(|r| (*r==length_observation_ref(a)) != cfg!(NGL_invert))]
#[kani::modifies()]
fn observed_length(a:&OwnedAccount)->[usize;2]{length_observation(a.data_len())}
#[kani::proof_for_contract(observed_length)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_observed_contract(){let mut a=core::mem::ManuallyDrop::new(account());let tag:u8=kani::any();kani::assume(tag<3);a.length=match tag{0=>Ok(kani::any()),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)};let _=observed_length(&a);}
'''
update({P+'NGL_owned.rs':s},'observed_length_carrier')
q=[]
for i,(t,bad) in enumerate([('length_observed_contract',0),('length_observed_contract',1),('checkpoint_contract',0),('checkpoint_contract',1)],43):q.append(dict(attempt=f'NGL_K{i:03}',kind='kani',target='r1_pool_adapter::owned::NGL_owned::'+t,expected=bad,env={'NGL_INVERT':'1'} if bad else {}))
for i,(t,bad,profile) in enumerate([('copy32_correct',0,0),('copy32_wrong',1,0),('copy32_correct',0,1),('copy32_wrong',1,1)],47):q.append(dict(attempt=f'NGL_K{i:03}',kind='kani',target='r1_pool_adapter::NGL_adapter::'+t,expected=bad,env={'NGL_INVERT':'1'} if profile else {}))
(E/'NGL_OBSERVED_CONTRACT_QUEUE.json').write_text(json.dumps(q,indent=1)+'\n')
