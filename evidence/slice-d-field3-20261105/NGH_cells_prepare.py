"""Generate source-derived one-cell cuts without printing source."""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent
raw=subprocess.check_output(['git','show','4bb3b3f5:crates/aspis-core/src/field.rs'],text=True)
def body(text,name):
 p=text.index(name);b=text.index('{',p);d=1;j=b+1
 while d:d+=(text[j]=='{')-(text[j]=='}');j+=1
 return text[b+1:j-1]
b=body(raw,'fn qm31_accumulate_product_channels(')
pre=b[:b.index('    for component')]
update='sums[component][channel] += left_components[component][channel].0 as u64\n                * right_components[component][channel].0 as u64;'
assert update in b
s='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
const NGH_P:u64=2147483647;
fn any_q()->QM31 {QM31 {c0:CM31 {a:M31(kani::any()),b:M31(kani::any())},c1:CM31 {a:M31(kani::any()),b:M31(kani::any())}}}
fn canonical(q:QM31)->bool {q.c0.a.0<NGH_P as u32 && q.c0.b.0<NGH_P as u32 && q.c1.a.0<NGH_P as u32 && q.c1.b.0<NGH_P as u32}
#[inline(never)]
fn native_product(a:u64,b:u64)->u64 { a*b }
fn product_stub(a:u64,b:u64)->u64 {
 kani::assume(a<NGH_P && b<NGH_P);
 let reply:u64=kani::any(); kani::assume(reply==a*b);reply
}
fn bound(s:[[u64;3];3],i:usize,j:usize,l:QM31,r:QM31)->bool {canonical(l)&&canonical(r)&&s[i][j]<=3*(NGH_P-1)*(NGH_P-1)}
'''
associations=[]
for i in range(3):
 for j in range(3):
  n=f'{i}{j}'
  cut=pre+f'    let component={i}; let channel={j};\n    '+update.replace('left_components[component][channel].0 as u64\n                * right_components[component][channel].0 as u64','native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64)')+'\n    sums\n'
  reference=pre+f'    sums[{i}][{j}] += native_product(left_components[{i}][{j}].0 as u64,right_components[{i}][{j}].0 as u64);\n    sums\n'
  s+=f'fn ref_{n}(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {{'+reference+'}\n'
  s+=f'''#[kani::requires(bound(sums,{i},{j},left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {{out[{i}][{j}] != ref_{n}(sums,left,right)[{i}][{j}]}} else {{out[{i}][{j}] == ref_{n}(sums,left,right)[{i}][{j}]}})]
fn cell_{n}(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {{'''+cut+'}\n'
  s+=f'''#[kani::proof_for_contract(cell_{n})]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn proof_{n}() {{let sums=kani::any();let left=any_q();let right=any_q();cell_{n}(sums,left,right);}}
'''
  associations.append(dict(cell=[i,j],frozen_prelude_identical=True,selected_update_identical_modulo_opaque_product=True,reference_same_cache=True,native_product_count=1))
s+='''#[kani::proof]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn frame() {
 let sums:[[u64;3];3]=kani::any();let left=any_q();let right=any_q();
 kani::assume(bound(sums,0,0,left,right));let out=cell_00(sums,left,right);
 let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3&&(i!=0||j!=0));
 assert!(if cfg!(NGH_invert) {out[i][j]!=sums[i][j]} else {out[i][j]==sums[i][j]});
}
'''
(E/'NGH_cells.rs.txt').write_text(s)
d=json.loads((E/'NGH_NATIVE_INPUTS.json').read_text());field='crates/aspis-core/src/field.rs';d[field]+='\n#[cfg(kani)]\nmod NGH_cells;\n';d['crates/aspis-core/src/field/NGH_cells.rs']=s
(E/'NGH_CELL_INPUTS.json').write_text(json.dumps(d));(E/'NGH_CELL_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest() for n,t in d.items()},indent=1)+'\n')
(E/'NGH_CELL_ASSOCIATION.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_field_sha256=hashlib.sha256(raw.encode()).hexdigest(),generated_sha256=hashlib.sha256(s.encode()).hexdigest(),cells=associations,write_frame='only selected cell assigned; owned matrix, no external writes',status='source association only; native/model admission pending'),indent=1)+'\n')
print('Generated nine one-cell cuts and frame; source suppressed.')
