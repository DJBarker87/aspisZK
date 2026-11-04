from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;x=json.loads((E/'NGH_NATIVE_INPUTS.json').read_text())
name='crates/aspis-core/src/NGH_reference.rs';r=x[name]
# Prefix-owned scalar wrapper is exactly the original primitive product; Kani
# replaces it with a nondeterministic value constrained by NFT_Dot.scalar_product.
r+='''
pub(super) fn native_product(a:u64,b:u64)->u64{a*b}
pub(super) fn product_stub(a:u64,b:u64)->u64{assert!(a<P as u64&&b<P as u64);let p:u64=kani::any();kani::assume(p==a*b&&p<=4611686009837453316);p}
fn one(now:u64,old:u64,a:M31,b:M31,done:bool)->bool{now==old+if done{native_product(a.0 as u64,b.0 as u64)}else{0}}
pub(super) fn progress(s:[[u64;3];3],old:[[u64;3];3],l:[[M31;3];3],r:[[M31;3];3],row:usize,col:usize)->bool{
PROGRESS
}
pub(super) fn row_progress(s:[[u64;3];3],old:[[u64;3];3],l:[[M31;3];3],r:[[M31;3];3],row:usize,col:usize)->bool{
ROW_PROGRESS
}
'''
r=r.replace('PROGRESS\n',' &&\n'.join(f' one(s[{i}][{j}],old[{i}][{j}],l[{i}][{j}],r[{i}][{j}],{i}<row||{i}==row&&{j}<col)' for i in range(3)for j in range(3))+'\n',1)
r=r.replace('ROW_PROGRESS\n',' &&\n'.join(f' one(s[{i}][{j}],old[{i}][{j}],l[{i}][{j}],r[{i}][{j}],{i}==row&&{j}<col)' for i in range(3)for j in range(3))+'\n',1)
# Replace only the exact product expression in both functions.
product='left_components[component][channel].0 as u64\n                * right_components[component][channel].0 as u64'
replacement='NGH_reference::native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64)'
field=x['crates/aspis-core/src/field.rs'];assert field.count(product)==1;field=field.replace(product,replacement)
a=field.index('fn qm31_accumulate_product_channels(');b=field.index('    for component in 0usize..3usize',a)
field=field[:b]+'    #[cfg_attr(NGH_for_diagnostic,kani::loop_invariant(NGH_reference::progress(sums,on_entry(sums),left_components,right_components,kani::index,0)))]\n'+field[b:]
b=field.index('        for channel in 0usize..3usize',a);field=field[:b]+'        #[cfg_attr(NGH_for_diagnostic,kani::loop_invariant(NGH_reference::row_progress(sums,on_entry(sums),left_components,right_components,component,kani::index)))]\n'+field[b:]
# Ensure the intended actual helper harness has KMX and paired primitive stub.
r=r.replace('#[kani::proof_for_contract(qm31_accumulate_product_channels)]','''#[kani::proof_for_contract(qm31_accumulate_product_channels)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,super::NGH_contracts::KMX_copy_nonoverlapping)]
#[kani::unwind(80)]''')
# KMX item is private to contracts; include the exact stub in the reference module instead.
r='include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'+r
r=r.replace('super::NGH_contracts::KMX_copy_nonoverlapping','KMX_copy_nonoverlapping')
x[name]=r;x['crates/aspis-core/src/field.rs']=field
(E/'NGH_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');(E/'NGH_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()},indent=1)+'\n')
(E/'NGH_reference_loop.rs.txt').write_text(r)
