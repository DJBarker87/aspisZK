"""Small deployed-code carrier observations; no field multiplication."""
from NEY_native_patch import E,frozen,program
import sys,json,subprocess
shape,mode=sys.argv[1:];assert shape in ['limbs','tag'] and mode in ['positive','value']
subprocess.run([sys.executable,str(E/'NEY_prepare_window.py'),'1','positive'],check=True)
if shape=='limbs':
 p='crates/aspis-core/src/field/wide_exact.rs';f=frozen(p);a=f.index('    pub const fn to_limbs(');z=f.index('\n    }',a)+6;original=f[a:z]
 code='let limbs:[u32;8]=kani::any();kani::assume(limbs.iter().all(|x|*x<aspis_core::field::P));let value=aspis_core::field::wide_exact::WideExact::from_limbs(limbs).unwrap();let i:usize=kani::any();kani::assume(i<8);assert!(value.to_limbs()[i]==limbs[i]@BAD@);'
 domain='all canonical eight-limb carriers and arbitrary observed limb; from_limbs is input construction, not a new slice callee bridge'
else:
 p='crates/aspis-r1-cost-probe/src/transport.rs';f=frozen(p);a=f.index('    pub fn tag(');z=f.index('\n',a);original=f[a:z]
 code='use aspis_r1_cost_probe::transport::Variant;let selector:u8=kani::any();kani::assume(selector<3);let value=match selector{0=>Variant::S1,1=>Variant::S2,_=>Variant::D};assert!(value.tag()==(selector+1)@BAD@);'
 domain='all three actual Variant constructors; selected frozen S2 root is the selector1 instance'
code=code.replace('@BAD@','^1' if mode=='value' else '')
body='''use super::*;
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEY_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NEY_KMX::KMX_copy_from_slice)]
fn scalar(){'''+code+'}\n'
# Keep setup canonicality as eight scalar constraints, not a native loop proof.
body=body.replace('limbs.iter().all(|x|*x<aspis_core::field::P)','&&'.join(f'limbs[{i}]<aspis_core::field::P' for i in range(8)))
program(body,'NEY_scalar')
(E/'NEY_SCALAR_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,frozen_path=p,frozen_body=original,source=body,domain=domain,classification='actual frozen scalar/fixed-array call under deployed features; inherited model/domain/physical association still required for composition credit'),indent=1)+'\n')
