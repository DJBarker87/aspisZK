from NGL_prepare import E,P,update
import json,re
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'r1_pool_adapter_owned.rs'];A=json.loads((E/'NGL_CONTRACT_ANNOTATIONS.json').read_text())
attrs={
 '    fn data_len(&self) -> Result<usize, ProgramError> {':'    #[cfg_attr(kani,kani::requires(NGL_owned::snapshot_domain(self)))]\n    #[cfg_attr(kani,kani::ensures(|r| NGL_owned::same_length(r,&self.length) != cfg!(NGL_false_length)))]\n    #[cfg_attr(kani,kani::modifies())]\n',
 '    fn data(&self) -> Result<&[u8], ProgramError> {':'    #[cfg_attr(kani,kani::requires(NGL_owned::snapshot_domain(self)))]\n    #[cfg_attr(kani,kani::ensures(|r| NGL_owned::data_matches(r,self) != cfg!(NGL_false_data)))]\n    #[cfg_attr(kani,kani::modifies())]\n',
 'fn require_verifier_checkpoint(account: &OwnedAccount, program_id: &Pubkey, writable: bool) -> ProgramResult {':'#[cfg_attr(kani,kani::requires(NGL_owned::snapshot_domain(account)))]\n#[cfg_attr(kani,kani::ensures(|r| NGL_owned::checkpoint_matches(r,account,program_id,writable) != cfg!(NGL_false_checkpoint)))]\n#[cfg_attr(kani,kani::modifies())]\n'
}
for sig,attr in attrs.items():assert s.count(sig)==1;s=s.replace(sig,attr+sig,1)
# Preserve historical annotations for exact erasure of earlier source snapshots.
for sig,attr in attrs.items():A['actual_scope '+sig]=attr
h=I[P+'NGL_owned.rs'];h+='''
pub(super) fn data_matches(r:&Result<&[u8],ProgramError>,a:&OwnedAccount)->bool{match(r,&a.bytes){(Ok(b),Ok(v))=>b.as_ptr()==v.as_ptr()&&b.len()==v.len(),(Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))=>true,(Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))=>true,_=>false}}
pub(super) fn checkpoint_matches(r:&ProgramResult,a:&OwnedAccount,p:&Pubkey,w:bool)->bool{let tag=if a.owner!=*p||a.is_signer||a.executable||a.is_writable!=w{2}else{match &a.length{Ok(n)if *n==1768=>0,Err(ProgramError::AccountBorrowFailed)=>1,_=>2}};match r{Ok(())=>tag==0,Err(ProgramError::AccountBorrowFailed)=>tag==1,Err(ProgramError::InvalidAccountData)=>tag==2,_=>false}}
'''
ctor='''let mut a=core::mem::ManuallyDrop::new(account());
#[cfg(NGL_record_borrow)]{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);}
#[cfg(NGL_record_rejected)]{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}
#[cfg(all(not(NGL_record_borrow),not(NGL_record_rejected)))]{let n:usize=kani::any();kani::assume(n<=58295);let mut v=kani::vec::exact_vec::<u8,58295>();v.truncate(n);a.length=Ok(n);a.bytes=Ok(v);}
'''
# The original actual-function harness names are retained; only the case split
# and observation lifetime change. No observer-induced drop follows the return.
for name,call in [('length_contract','a.data_len()'),('checkpoint_contract','require_verifier_checkpoint(&a,&Pubkey::new_from_array(kani::any()),kani::any())')]:
 pattern=r'(#\[cfg\(any\(\)\)\]\n)(#\[kani::proof_for_contract\([^\n]*\)\][^\n]*\n#\[kani::stub\([^\n]*\)\]\n)fn '+name+r'\(\)\{[^\n]*\}\n'
 replacement=r'\2fn '+name+'(){'+ctor+'let _=core::mem::ManuallyDrop::new('+call+');}\n'
 h,n=re.subn(pattern,lambda m:m.group(2)+'fn '+name+'(){'+ctor+'let _=core::mem::ManuallyDrop::new('+call+');}\n',h);assert n==1,(name,n)
h+='''
#[kani::proof_for_contract(OwnedAccount::data)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_actual_contract(){'''+ctor+'''let _=core::mem::ManuallyDrop::new(a.data());}
'''
update({P+'r1_pool_adapter_owned.rs':s,P+'NGL_owned.rs':h},'actual_return_scope_contracts');(E/'NGL_CONTRACT_ANNOTATIONS.json').write_text(json.dumps(A,indent=1)+'\n')
p=E/'NGL_run.py';t=p.read_text();needle="if os.environ.get('NGL_RECORD_CASE') in ['borrow','rejected']:env['RUSTFLAGS']+=' --cfg NGL_record_'+os.environ['NGL_RECORD_CASE']";t=t.replace(needle,needle+"\n if os.environ.get('NGL_FALSE_TARGET') in ['length','data','checkpoint']:env['RUSTFLAGS']+=' --cfg NGL_false_'+os.environ['NGL_FALSE_TARGET']");p.write_text(t)
q=[];i=61
for case in ['borrow','default','rejected']:
 for name,false_target in [('length_contract','length'),('data_actual_contract','data'),('checkpoint_contract','checkpoint')]:
  for bad in [0,1]:
   env={'NGL_RECORD_CASE':case};env.update({'NGL_FALSE_TARGET':false_target}if bad else{});q.append(dict(attempt=f'NGL_K{i:03}',kind='kani',target='r1_pool_adapter::owned::NGL_owned::'+name,expected=bad,env=env));i+=1
(E/'NGL_ACTUAL_SCOPE_QUEUE.json').write_text(json.dumps(q,indent=1)+'\n')
