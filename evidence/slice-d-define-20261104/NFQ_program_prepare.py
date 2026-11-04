from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];C='programs/r1-cost-probe/src/'
ref='''// Total safe scalar/scan references; the scan is proved by induction.
pub fn readonly_buffer_ref(signer:bool,writable:bool,executable:bool)->bool{!(signer||writable||executable)}
pub fn zero_step_ref(byte:u8)->bool{byte==0}
pub fn zero_ref(bytes:&[u8])->bool{
 let mut i=0;let mut all=true;
 while i<bytes.len() && all {all=bytes[i]==0;i+=1;}all
}
'''
base=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+C+'r1_pool_adapter.rs'],cwd=R,text=True)
needle='fn readonly_buffer_meta_ok(\n';assert base.count(needle)==1
attr='''#[cfg_attr(kani, kani::modifies())]
#[cfg_attr(kani, kani::ensures(|r| ((r.is_ok() == NFQ_program::reference::readonly_buffer_ref(is_signer,is_writable,executable)) && (r.is_ok() || matches!(r,Err(ProgramError::InvalidAccountData)))) != cfg!(NFQ_invert)))]
'''
s=base.replace(needle,attr+needle,1)+'\n#[cfg(kani)]\n#[path="NFQ_program.rs"]\nmod NFQ_program;\n'
code='''use super::*;
#[path="NFQ_scan_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(readonly_buffer_meta_ok)]
fn readonly_contract(){let _=readonly_buffer_meta_ok(kani::any(),kani::any(),kani::any());}
'''
files={C+'r1_pool_adapter.rs':s,C+'NFQ_program.rs':code,C+'NFQ_scan_reference.rs':ref}
(E/'NFQ_scan_reference.rs.txt').write_text(ref)
inputs=json.loads((E/'NFQ_NATIVE_INPUTS.json').read_text());inputs.update(files);(E/'NFQ_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NFQ_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NFQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,s in files.items():patch+=difflib.unified_diff(base.splitlines(True) if n.endswith('r1_pool_adapter.rs') else [],s.splitlines(True),fromfile='a/'+n if n.endswith('r1_pool_adapter.rs') else '/dev/null',tofile='b/'+n)
(E/'NFQ_program.patch').write_text(''.join(patch))
