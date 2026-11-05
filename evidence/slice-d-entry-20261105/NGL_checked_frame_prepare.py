from NGL_prepare import E,P,update
import json,re
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'NGL_owned.rs']
ctor='''let mut a=core::mem::ManuallyDrop::new(account());
#[cfg(NGL_record_borrow)]{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);}
#[cfg(NGL_record_rejected)]{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}
#[cfg(all(not(NGL_record_borrow),not(NGL_record_rejected)))]{let n:usize=kani::any();kani::assume(n<=58295);let mut v=kani::vec::exact_vec::<u8,58295>();v.truncate(n);a.length=Ok(kani::any());a.bytes=Ok(v);}
'''
# Existing input allocations precede the checked function. Empty modifies now
# protects the ENTIRE old heap, including all payload bytes, rather than comparing
# two symbolic 58k-byte observations through a returned temporary record.
start=s.index('#[kani::ensures(|r|*r)] #[kani::modifies()]\nfn length_record')
s=s[:start]+'''
fn bytes_domain(a:&OwnedAccount)->bool{matches!(&a.bytes,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData))}
#[kani::requires(length_domain(&a.length))] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn length_record(a:&OwnedAccount)->bool{let expected=length_observation_ref(a);let actual=length_observation(a.data_len());let mut tag=expected[0];if cfg!(NGL_invert){tag^=128;}actual[0]==tag&&actual[1]==expected[1]}
#[kani::proof_for_contract(length_record)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_record_contract(){'''+ctor+'''let _=length_record(&a);}
#[kani::requires(bytes_domain(a))] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn data_record(a:&OwnedAccount)->bool{let(tag,p,n)=match &a.bytes{Ok(v)=>(0,v.as_ptr()as usize,v.len()),Err(ProgramError::AccountBorrowFailed)=>(1,0,0),Err(ProgramError::InvalidAccountData)=>(2,0,0),_=>(3,0,0)};let mut expected=tag;if cfg!(NGL_invert){expected^=128;}match a.data(){Ok(b)=>expected==0&&b.as_ptr()as usize==p&&b.len()==n,Err(ProgramError::AccountBorrowFailed)=>expected==1,Err(ProgramError::InvalidAccountData)=>expected==2,Err(_)=>false}}
#[kani::proof_for_contract(data_record)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_record_contract(){'''+ctor+'''let _=data_record(&a);}
#[kani::requires(checkpoint_domain(a))] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn checkpoint_record(a:&OwnedAccount,program:&Pubkey,writable:bool)->bool{let expected=checkpoint_ref(a,program,writable);let mut tag=match expected{Ok(())=>0,Err(ProgramError::AccountBorrowFailed)=>1,Err(ProgramError::InvalidAccountData)=>2,_=>3};if cfg!(NGL_invert){tag^=128;}match require_verifier_checkpoint(a,program,writable){Ok(())=>tag==0,Err(ProgramError::AccountBorrowFailed)=>tag==1,Err(ProgramError::InvalidAccountData)=>tag==2,Err(_)=>false}}
#[kani::proof_for_contract(checkpoint_record)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_record_contract(){'''+ctor+'''let program=Pubkey::new_from_array(kani::any());let _=checkpoint_record(&a,&program,kani::any());}
'''
update({P+'NGL_owned.rs':s},'protected_old_heap_frame')
q=[];i=49
for case in ['default','borrow','rejected']:
 for target in ['length_record_contract','data_record_contract','checkpoint_record_contract']:
  for bad in [0,1]:
   env={'NGL_RECORD_CASE':case};env.update({'NGL_INVERT':'1'}if bad else {});q.append(dict(attempt=f'NGL_K{i:03}',kind='kani',target='r1_pool_adapter::owned::NGL_owned::'+target,expected=bad,env=env));i+=1
(E/'NGL_PROTECTED_FRAME_QUEUE.json').write_text(json.dumps(q,indent=1)+'\n')
