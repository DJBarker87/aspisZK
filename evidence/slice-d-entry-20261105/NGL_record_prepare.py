from NGL_prepare import update,E,P
import json
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'NGL_owned.rs'];s+='''
#[derive(PartialEq,Eq)]
struct NGL_Frame{key:[u8;32],owner:[u8;32],signer:bool,writable:bool,executable:bool,length_tag:u8,length_value:usize,bytes_tag:u8,pointer:usize,length:usize,capacity:usize,cell:u8}
fn frame(a:&OwnedAccount,j:usize)->NGL_Frame{
 let(lt,lv)=match &a.length{Ok(n)=>(0,*n),Err(ProgramError::AccountBorrowFailed)=>(1,0),Err(ProgramError::InvalidAccountData)=>(2,0),_=>(3,0)};
 let(bt,p,n,c,v)=match &a.bytes{Ok(b)=>(0,b.as_ptr()as usize,b.len(),b.capacity(),if b.is_empty(){0}else{b[j]}),Err(ProgramError::AccountBorrowFailed)=>(1,0,0,0,0),Err(ProgramError::InvalidAccountData)=>(2,0,0,0,0),_=>(3,0,0,0,0)};
 NGL_Frame{key:a.key.to_bytes(),owner:a.owner.to_bytes(),signer:a.is_signer,writable:a.is_writable,executable:a.executable,length_tag:lt,length_value:lv,bytes_tag:bt,pointer:p,length:n,capacity:c,cell:v}
}
fn record_account(checkpoint:bool)->core::mem::ManuallyDrop<OwnedAccount>{
 let mut a=account();let length_case:u8=kani::any();kani::assume(length_case<if checkpoint{2}else{3});a.length=match length_case{0=>Ok(kani::any()),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)};
 let n:usize=kani::any();kani::assume(n<=58295);let mut bytes=kani::vec::exact_vec::<u8,58295>();bytes.truncate(n);let bytes_case:u8=kani::any();kani::assume(bytes_case<3);a.bytes=match bytes_case{0=>Ok(bytes),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)};
 core::mem::ManuallyDrop::new(a)
}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn length_record()->bool{let a=record_account(false);let j:usize=kani::any();let n=a.bytes.as_ref().map(|b|b.len()).unwrap_or(0);kani::assume(if n==0{j==0}else{j<n});let before=frame(&a,j);let result=a.data_len();let mut tag=before.length_tag;if cfg!(NGL_invert){tag^=128;}let exact=match result{Ok(n)=>tag==0&&n==before.length_value,Err(ProgramError::AccountBorrowFailed)=>tag==1,Err(ProgramError::InvalidAccountData)=>tag==2,Err(_)=>false};exact&&frame(&a,j)==before}
#[kani::proof_for_contract(length_record)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_record_contract(){let _=length_record();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn data_record()->bool{let a=record_account(false);let j:usize=kani::any();let n=a.bytes.as_ref().map(|b|b.len()).unwrap_or(0);kani::assume(if n==0{j==0}else{j<n});let before=frame(&a,j);let result=a.data();let mut tag=before.bytes_tag;if cfg!(NGL_invert){tag^=128;}let exact=match result{Ok(b)=>tag==0&&b.as_ptr()as usize==before.pointer&&b.len()==before.length&&(if b.is_empty(){0}else{b[j]})==before.cell,Err(ProgramError::AccountBorrowFailed)=>tag==1,Err(ProgramError::InvalidAccountData)=>tag==2,Err(_)=>false};exact&&frame(&a,j)==before}
#[kani::proof_for_contract(data_record)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_record_contract(){let _=data_record();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn checkpoint_record()->bool{let a=record_account(true);let j:usize=kani::any();let n=a.bytes.as_ref().map(|b|b.len()).unwrap_or(0);kani::assume(if n==0{j==0}else{j<n});let before=frame(&a,j);let program=Pubkey::new_from_array(kani::any());let writable:bool=kani::any();let invalid=a.owner!=program||a.is_signer||a.executable||a.is_writable!=writable;let mut expected=if invalid{2}else if before.length_tag==1{1}else if before.length_value!=1768{2}else{0};if cfg!(NGL_invert){expected^=128;}let r=require_verifier_checkpoint(&a,&program,writable);let exact=match r{Ok(())=>expected==0,Err(ProgramError::AccountBorrowFailed)=>expected==1,Err(ProgramError::InvalidAccountData)=>expected==2,Err(_)=>false};exact&&frame(&a,j)==before}
#[kani::proof_for_contract(checkpoint_record)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_record_contract(){let _=checkpoint_record();}
'''
update({P+'NGL_owned.rs':s},'complete_local_records')
q=[]
for i,t in enumerate(['length_record_contract','data_record_contract','checkpoint_record_contract']):
 for bad in [0,1]:q.append(dict(attempt=f'NGL_K{46+2*i+bad:03}',kind='kani',target='r1_pool_adapter::owned::NGL_owned::'+t,expected=bad,env={'NGL_INVERT':'1'}if bad else {}))
(E/'NGL_RECORD_QUEUE.json').write_text(json.dumps(q,indent=1)+'\n')
