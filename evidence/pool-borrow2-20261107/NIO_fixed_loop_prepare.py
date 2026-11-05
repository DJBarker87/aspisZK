"""Split a timed-out variable-prefix job into exact admitted prefix sizes."""
from pathlib import Path
import sys,json,re,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E))
from NIO_native_prepare import stage,attrs,account_setup
from NIO_frozen_identity import frozen
text=frozen()['programs/aspis-pool/src/pair_forest.rs'].decode();statement=next(l.strip() for l in text.splitlines() if 'lane_data.push(' in l and 'try_borrow_mut_data' in l);var=re.search(r'push\((\w+)\.try_borrow_mut_data',statement).group(1)
n=int(sys.argv[1]);negative=sys.argv[2]=='negative';assert 0<=n<8
head="use super::*;\nfn NIO_step<'b,'i>(lane_data:&mut alloc::vec::Vec<core::cell::RefMut<'b,&'i mut [u8]>>,"+var+":&'b AccountInfo<'i>)->ProgramResult{\n"+statement+'\nOk(())}\n'
s=account_setup(n+2)
s+='let result=(||->ProgramResult{let _master_data=a'+str(n+1)+'.try_borrow_mut_data()?;let mut lane_data=alloc::vec::Vec::with_capacity(8);\n'
for i in range(n):s+=f'lane_data.push(a{i}.try_borrow_mut_data()?);\n'
s+=f'NIO_step(&mut lane_data,&a{n})?;assert!(lane_data.len()=={n+1});\n'
for i in range(n+2):s+=f'assert!(a{i}.try_borrow_mut_data().is_err());\n'
if negative:s+='let unreleased=match lane_data.pop(){Some(g)=>g,None=>{assert!(false);return Ok(())}};core::mem::forget(unreleased);\n'
s+='Ok(())})();assert!(result==Ok(()));\n'
for i in range(n+2):s+=f'assert!(a{i}.try_borrow_mut_data().is_ok());\n'
source=head+attrs()+'\n#[kani::proof]\nfn certificate(){'+s+'}\n'
stage('programs/aspis-pool/src/pair_forest.rs',source,'actual retained-guard source iteration, isolated prefix size',sys.argv[2],f'Exact valid typed prefix size {n}, source capacity eight, separately retained master guard; arbitrary scalar metadata and payload bytes; target initially free. One original native body iteration; prefix is harness pre-state construction.','Complete initializer prefix/domain, arbitrary failing target counter and full model/source graph association remain OPEN; no full function or Pool row claimed.',dict(member='process_pair_forest_initialize_with_runtime_v1',prefix_count=n,target_iterations=1,source_statement=statement,source_sha256=hashlib.sha256(text.encode()).hexdigest(),expected_verdict='FAIL' if negative else 'PASS',control='Forget the actual newly acquired guard; subsequent counter-restoration assertion must fail.'))
print('Fixed-prefix original source iteration prepared')
