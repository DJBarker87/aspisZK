from pathlib import Path
from NCV_instrument import harness_text
E=Path(__file__).resolve().parent
stubs=(E/'NCV_make_fragments.py').read_text().split("stubs='''",1)[1].split("'''",1)[0]
s='''#![allow(non_snake_case,dead_code)]
use super::*;
const NCV_INVERSE:bool=false;
fn NCV_any_checkpoint()->PoolV1PairForestCheckpointV1{
 PoolV1PairForestCheckpointV1{bump:kani::any(),master:kani::any(),deployment_domain:kani::any(),checkpoint_sequence:kani::any(),global_root:[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],lane_sequences:kani::any()}
}
#[kani::modifies()]
#[kani::ensures(|r:&Box<PoolV1PairForestCheckpointV1>| (**r==*a)!=NCV_INVERSE)]
fn NCV_box_copy(a:&PoolV1PairForestCheckpointV1)->Box<PoolV1PairForestCheckpointV1>{Box::new(*a)}
#[kani::modifies(x)]
#[kani::ensures(|r:&Box<PoolV1PairForestCheckpointV1>| **r==*a)]
fn NCV_box_frame(a:&PoolV1PairForestCheckpointV1,x:&mut u8,y:&mut u8)->Box<PoolV1PairForestCheckpointV1>{*x=1;if NCV_INVERSE{*y=2;}Box::new(*a)}
'''
for name in ['copy','frame']:
 s+='#[kani::proof_for_contract(NCV_box_'+name+')]\n'+stubs+'#[kani::unwind(34)]\nfn NCV_box_'+name+'_check(){let a=NCV_any_checkpoint();'
 s+=('let _=NCV_box_copy(&a);' if name=='copy' else 'let mut x=kani::any();let mut y=kani::any();let _=NCV_box_frame(&a,&mut x,&mut y);')+'}\n'
(E/'NCV_box.rs').write_text(s)
p=E/'NCV_native.rs';s=harness_text('NCV_native.rs')
if 'mod NCV_box;' not in s:s+='\n#[path="NCV_box.rs"] mod NCV_box;\n'
p.with_suffix('.tmp').write_text(s);p.with_suffix('.tmp').replace(p)
p=E/'NCV_instrument.py';s=p.read_text();line=" d['programs/r1-cost-probe/src/NCV_box.rs']=(E/'NCV_box.rs').read_text().replace('const NCV_INVERSE:bool=false;','const NCV_INVERSE:bool='+('true' if os.environ.get('NCV_NEGATIVE') else 'false')+';')\n"
if line not in s:s=s.replace(" case=os.environ.get('NCV_CASE')",line+" case=os.environ.get('NCV_CASE')")
p.write_text(s)
