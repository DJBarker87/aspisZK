"""One original retained-guard push, with a typed admitted prefix and controls."""
from pathlib import Path
import sys,json,re,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E))
from NIO_native_prepare import stage,attrs,account_setup
from NIO_frozen_identity import frozen
source_text=frozen()['programs/aspis-pool/src/pair_forest.rs'].decode()
original=next(l.strip() for l in source_text.splitlines() if 'lane_data.push(' in l and 'try_borrow_mut_data' in l)
lane_name=re.search(r'push\((\w+)\.try_borrow_mut_data',original).group(1)
case=sys.argv[1];negative=sys.argv[2]=='negative'
head="use super::*;\nfn NIO_step<'b,'i>(lane_data:&mut alloc::vec::Vec<core::cell::RefMut<'b,&'i mut [u8]>>,"+lane_name+":&'b AccountInfo<'i>)->ProgramResult{\n"+original+'\nOk(())}\n'
s=account_setup(10)
s+='let lanes=[&a0,&a1,&a2,&a3,&a4,&a5,&a6,&a7];let n:usize=kani::any();kani::assume(n<8);\n'
s+='let old=lanes[n].try_borrow_data().unwrap()[0];let result=(||->ProgramResult{let _master_data=a8.try_borrow_mut_data()?;let mut lane_data=alloc::vec::Vec::with_capacity(8);for i in 0..n{lane_data.push(lanes[i].try_borrow_mut_data().unwrap());}NIO_step(&mut lane_data,lanes[n])?;\n'
s+='assert!(lane_data.len()==n+1);assert!(a8.try_borrow_mut_data().is_err());\n'
if case=='new':
 if negative:s+='drop(lane_data.pop());lane_data.push(a9.try_borrow_mut_data().unwrap());\n'
 s+='assert!(lanes[n].try_borrow_mut_data().is_err());assert!(lane_data[n][0]==old);\n'
else:
 j=int(case)
 if negative:s+=f'if {j}<n {{let previous=core::mem::replace(&mut lane_data[{j}],a9.try_borrow_mut_data().unwrap());drop(previous);}}\n'
 s+=f'if {j}<n {{assert!(lanes[{j}].try_borrow_mut_data().is_err());}}\n'
s+='Ok(())})();assert!(result==Ok(()));\n'
for i in range(10):s+=f'assert!(a{i}.try_borrow_mut_data().is_ok());\n'
(E/'NIO_LOOP_SOURCE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',statement=original,statement_sha256=hashlib.sha256(original.encode()).hexdigest(),source_sha256=hashlib.sha256(source_text.encode()).hexdigest(),target_body_iterations=1,prestate_constructor='Typed existing prefix of 0..7 guards; fixed source capacity 8; separate retained master guard.',model_requirement='NIO_Nested.retained_step plus source-cell/key admission and KMX value/frame laws; full initializer and returning children remain OPEN.'),indent=2)+'\n')
source=head+attrs()+'\n#[kani::proof]\nfn certificate(){'+s+'}\n'
stage('programs/aspis-pool/src/pair_forest.rs',source,'actual retained-guard push, one iteration',sys.argv[2],'Arbitrary typed prefix count 0..7, actual fixed capacity 8, one retained master guard, arbitrary byte payloads and one original SDK acquisition/push; per-position observation.','Full initializer entry domain, all callee footprints, complete native/model graph association and error unwinding remain OPEN.',dict(member='process_pair_forest_initialize_with_runtime_v1',window=case,expected_verdict='FAIL' if negative else 'PASS',source_statement='NIO_LOOP_SOURCE.json'))
print('One retained-guard source iteration prepared')
