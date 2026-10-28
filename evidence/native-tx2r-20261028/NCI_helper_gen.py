from NCI_extend import extend,attrs
h='\n#[cfg(kani)] mod NCI_helpers {\nuse super::*;\n'
for name in ['weight_step','weight_empty','semantic_window','query_reject']:
 for wrong in [False,True]:
  h+=attrs+f'fn {name}_{"wrong" if wrong else "ok"}(){{\n'
  op='!=' if wrong else '=='
  if name=='weight_step':h+=f'''let bytes:[u8;64]=kani::any();let start:usize=kani::any();kani::assume(start<=48);
let expected=K::from_le_bytes(&bytes[start..start+16].try_into().unwrap());
let mut weights=Vec::with_capacity(1);weights.push(K::ZERO);
let out=read_checkpoint_weights(&bytes,start,weights);
assert!(out.is_ok(){op}expected.is_some());
if let Ok((weights,at))=out{{assert!(weights.len()==1&&at==start+16);assert!(Some(weights[0])==expected);}}
'''
  if name=='weight_empty':h+=f'''let bytes:[u8;64]=kani::any();let start:usize=kani::any();
let (weights,at)=read_checkpoint_weights(&bytes,start,Vec::new()).unwrap();
assert!(weights.len()==0);assert!(at{op}start);
'''
  if name=='semantic_window':h+=f'''let mut bytes=[0u8;160];let value:[u8;16]=kani::any();let slot:usize=kani::any();kani::assume(slot<10);
bytes[16*slot..16*slot+16].copy_from_slice(&value);
let expected=K::from_le_bytes(&value);let out=read_checkpoint_semantic_alpha(&bytes,0);
assert!(out.is_ok(){op}expected.is_some());
if let Ok((values,at))=out{{assert!(at==160);let j:usize=kani::any();kani::assume(j<10);assert!(values[j]==if j==slot{{expected.unwrap()}}else{{K::ZERO}});}}
'''
  if name=='query_reject':h+=f'''let queries:[u32;22]=kani::any();kani::assume(queries[0]>=1<<18);
let out=validate_checkpoint_queries(&queries);assert!(out.is_err(){op}true);
'''
  h+='}\n'
h+='}\n'
extend('NCI_helpers.patch',h)
