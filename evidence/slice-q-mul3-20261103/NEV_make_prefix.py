from pathlib import Path
import json,difflib
E=Path(__file__).resolve().parent;I=E.parent/'slice-q-mul2-20261101'
x={n.replace('NEI_','NEV_'):t.replace('NEI_','NEV_') for n,t in json.loads((I/'NEI_PAYLOAD.json').read_text()).items()}
p='crates/aspis-r1-cost-probe/src/NEV_prefix_step.rs'
# Keep predecessor functions archived unchanged in semantics; do not run them.
s=x[p]
s+='''
// Arbitrary valid prestate, built at fixed offsets. This is setup only.
// No fixed capacity, initialized-word restriction, custom allocator, or loop body.
#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_push_fixed_offsets() {
 let length:usize=kani::any();let index:usize=kani::any();
 kani::assume(length<=110 && index<length);
 let mut before:Vec<M31>=Vec::with_capacity(length);
 assert_eq!(before.capacity(),length);
 let initialized=before.as_mut_ptr();
'''
for i in range(110):s+=f' if {i}<index {{unsafe {{initialized.add({i}).write(M31(kani::any()));}}}}\n'
s+='''
 unsafe {before.set_len(index);}
 let pointer=before.as_ptr();let product=M31(kani::any());
 before.push(product);
 let appended=unsafe {before.as_ptr().add(index).read()}.0;
 assert_eq!(appended,if cfg!(NEV_wrong_fixed_offsets){product.0^1}else{product.0});
 assert!(before.len()==index+1 && before.capacity()==length && before.as_ptr()==pointer);
}
'''
x[p]=s
(E/'NEV_PREFIX_NATIVE.rs').write_text(s)
(E/'NEV_PAYLOAD.json').write_text(json.dumps(x))
frozen=json.loads((E/'NEV_FROZEN.json').read_text());patch=''
for n,t in x.items():
 if n.endswith('.lean'):continue
 patch+=''.join(difflib.unified_diff(frozen.get(n,'').splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NEV_native.patch').write_text(patch)
