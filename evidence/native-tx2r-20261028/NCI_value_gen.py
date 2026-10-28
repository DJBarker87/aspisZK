from NCI_extend import extend,attrs
h='''
#[cfg(kani)] mod NCI_value {
use super::*;
fn reduce(x:u64)->M31{let z:u32=kani::any();kani::assume(z as u64==x%2147483647);M31(z)}
'''
for name in ['value','finish']:
 for wrong in [False,True]:
  h+=attrs+'#[kani::stub(aspis_core::field::M31::reduce_u64,reduce)]\n'+f'fn {name}_{"wrong" if wrong else "ok"}(){{\n'
  h+='''let row:[u64;4]=kani::any();let mut raw=Vec::with_capacity(1);raw.push(row);let terms:usize=kani::any();let state=BatchedWeights{raw,terms};
'''
  if name=='value':h+='let out=state.value(0);\n'
  else:h+='let mut weights=[K::ZERO];state.finish(&mut weights);let out=weights[0];\n'
  h+='let values=[out.c0.a.0,out.c0.b.0,out.c1.a.0,out.c1.b.0];let j:usize=kani::any();kani::assume(j<4);\n'
  h+=f'assert!((values[j] as u64){"!=" if wrong else "=="}row[j]%2147483647);assert!(state.terms==terms&&state.raw[0][j]==row[j]);\n'
  h+='}\n'
h+='}\n'
extend('NCI_value.patch',h)
