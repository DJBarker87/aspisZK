"""Original loop-step error arm under an admitted typed retained prefix."""
from pathlib import Path
import sys,json,re,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E))
from NIO_native_prepare import stage,attrs,account_setup
from NIO_frozen_identity import frozen
text=frozen()['programs/aspis-pool/src/pair_forest.rs'].decode();statement=next(l.strip() for l in text.splitlines() if 'lane_data.push(' in l and 'try_borrow_mut_data' in l);var=re.search(r'push\((\w+)\.try_borrow_mut_data',statement).group(1)
negative=sys.argv[1]=='negative';n=4
head="use super::*;\nfn NIO_step<'b,'i>(lane_data:&mut alloc::vec::Vec<core::cell::RefMut<'b,&'i mut [u8]>>,"+var+":&'b AccountInfo<'i>)->ProgramResult{\n"+statement+'\nOk(())}\n'
s=account_setup(6)
s+='let shared:bool=kani::any();let external_shared=if shared {Some(a4.try_borrow_data().unwrap())}else{None};let external_exclusive=if shared {None}else{Some(a4.try_borrow_mut_data().unwrap())};\n'
s+='let result=(||->ProgramResult{let master_data=a5.try_borrow_mut_data()?;let mut lane_data=alloc::vec::Vec::with_capacity(8);\n'
for i in range(n):s+=f'lane_data.push(a{i}.try_borrow_mut_data()?);\n'
s+='let result=NIO_step(&mut lane_data,&a4);assert!(result==Err(ProgramError::AccountBorrowFailed));assert!(lane_data.len()==4);\n'
for i in range(6):s+=f'assert!(a{i}.try_borrow_mut_data().is_err());\n'
if negative:s+='core::mem::forget(master_data);\n'
s+='result})();assert!(result==Err(ProgramError::AccountBorrowFailed));\n'
for i in [0,1,2,3,5]:s+=f'assert!(a{i}.try_borrow_mut_data().is_ok());\n'
s+='assert!(a4.try_borrow_mut_data().is_err());drop(external_shared);drop(external_exclusive);assert!(a4.try_borrow_mut_data().is_ok());\n'
source=head+attrs()+'\n#[kani::proof]\nfn certificate(){'+s+'}\n'
stage('programs/aspis-pool/src/pair_forest.rs',source,'actual retained-guard source iteration: blocked target error arm',sys.argv[1],'Typed retained prefix of four guards and a separate master guard; target has one external shared or exclusive guard; source capacity eight.','Other failed-prefix sizes and arbitrary numeric ambient counter need the SDK model/source association; full initializer and Pool row remain OPEN.',dict(member='process_pair_forest_initialize_with_runtime_v1',prefix_count=4,target_iterations=1,source_statement=statement,source_sha256=hashlib.sha256(text.encode()).hexdigest(),expected_verdict='FAIL' if negative else 'PASS',observed_result='Err(AccountBorrowFailed)',control='Forget the live master guard on the error path; counter-restoration assertion must fail.'))
print('Retained-guard acquisition error arm prepared')
