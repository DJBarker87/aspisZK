from NCI_extend import extend,attrs
h='\n#[cfg(kani)] mod NCI_pending {\nuse super::*;\n'
q='K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}'
for name in ['residue','power','basis','weight','new']:
 for wrong in [False,True]:
  h+=attrs+f'fn {name}_{"wrong" if wrong else "ok"}(){{\n'
  op='!=' if wrong else '=='
  if name=='residue':h+=f'let a:[u64;4]=kani::any();let i:usize=kani::any();kani::assume(i<4);assert!(residue_limb_at(&a,i){op}a[i]);\n'
  if name=='power':h+=f'let a:[u32;4]=kani::any();let i:usize=kani::any();kani::assume(i<4);assert!(power_limb_at(&a,i){op}a[i]);\n'
  if name=='basis':h+='let a=['+','.join(['M31(kani::any())']*256)+f'];let i:usize=kani::any();kani::assume(i<256);assert!(basis_at(&a,i){op}a[i]);\n'
  if name=='weight':h+='let a=['+','.join([q]*64)+f'];let i:usize=kani::any();kani::assume(i<64);assert!(accumulated_weight_at(&a,i){op}a[i]);\n'
  if name=='new':h+=f'''let w={q};let out=BatchedWeights::new(&[w]).unwrap();
assert!(out.terms==0&&out.raw.len()==1);let i:usize=kani::any();kani::assume(i<4);
let expected=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];assert!(out.raw[0][i]{op}expected[i]);\n'''
  h+='}\n'
h+='}\n'
extend('NCI_pending.patch',h)
