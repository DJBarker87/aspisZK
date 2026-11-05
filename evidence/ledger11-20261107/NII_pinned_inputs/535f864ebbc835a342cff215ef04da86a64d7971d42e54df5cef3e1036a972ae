from NGL_prepare import update,E,P
import json,re
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'NGL_owned.rs']
name='length_contract';pat=r'fn length_contract\(\)\{[^\n]*\}\n';old=re.search(pat,s);assert old
base='let mut a=core::mem::ManuallyDrop::new(account());a.length=Err(ProgramError::AccountBorrowFailed);let _=a.data_len();'
s=s[:old.start()]+'fn length_contract(){'+base+'}\n'+s[old.end():]
attrs='''#[kani::proof_for_contract(OwnedAccount::data_len)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
for label,value in [('length_contract_ok','Ok(kani::any())'),('length_contract_invalid','Err(ProgramError::InvalidAccountData)')]:s+='\n'+attrs+'fn '+label+'(){let mut a=core::mem::ManuallyDrop::new(account());a.length='+value+';let _=a.data_len();}\n'
update({P+'NGL_owned.rs':s},'length_case_partition')
q=[]
for i,t in enumerate(['length_contract','length_contract_ok','length_contract_invalid']):
 for bad in [0,1]:q.append(dict(attempt=f'NGL_K{44+2*i+bad:03}',kind='kani',target='r1_pool_adapter::owned::NGL_owned::'+t,expected=bad,env={'NGL_INVERT':'1'}if bad else {}))
(E/'NGL_LENGTH_PARTITION_QUEUE.json').write_text(json.dumps(q,indent=1)+'\n')
