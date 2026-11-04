"""Finite capacity partition; no single capacity is accepted as caller coverage."""
from pathlib import Path
import sys,json,difflib
E=Path(__file__).resolve().parent;lo,hi=map(int,sys.argv[1:3]);stride=int(sys.argv[3]) if len(sys.argv)>3 else 1;assert stride in [1,5];assert 1<=lo<=hi<=110
if (lo,hi)==(17,32):raise SystemExit('STOP campaign before next launch: refine to actual five-element gather capacities')
x=json.loads((E/'NEV_PAYLOAD.json').read_text());n='crates/aspis-r1-cost-probe/src/NEV_prefix_step.rs'
s=json.loads((E.parent/'slice-q-mul2-20261101/NEI_PAYLOAD.json').read_text())['crates/aspis-r1-cost-probe/src/NEI_prefix_step.rs'].replace('NEI_','NEV_')
s+='''// Exact Kani arbitrary initialized allocation. Truncation only drops u32 wrappers.
fn NEV_append_fixed_capacity<const CAP:usize>() {
 let mut before=kani::vec::exact_vec::<M31,CAP>();
 let index:usize=kani::any();let observed:usize=kani::any();
 kani::assume(index<CAP && observed<=index);
 before.truncate(index);
 let product=M31(kani::any());let old=if observed<index{before[observed].0}else{product.0};
 let pointer=before.as_ptr();
 before.push(product);
 let after=before[observed].0;
 assert_eq!(after,if cfg!(NEV_wrong_fixed_offsets){old^1}else{old});
 assert!(before.len()==index+1 && before.capacity()==CAP && before.as_ptr()==pointer);
}
#[kani::proof] #[kani::unwind(444)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_push_fixed_offsets() {
 let length:usize=kani::any();
'''
s+=f' kani::assume({lo}<=length && length<={hi} && (length-{lo})%{stride}==0);\n match length {{\n'
for cap in range(lo,hi+1,stride):s+=f' {cap}=>NEV_append_fixed_capacity::<{cap}>(),\n'
s+=' _=>unreachable!(),\n }\n}\n'
x[n]=s;(E/'NEV_PREFIX_NATIVE.rs').write_text(s);(E/'NEV_PAYLOAD.json').write_text(json.dumps(x))
frozen=json.loads((E/'NEV_FROZEN.json').read_text());patch=''
for n,t in x.items():
 if n.endswith('.lean'):continue
 patch+=''.join(difflib.unified_diff(frozen.get(n,'').splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NEV_native.patch').write_text(patch)
(E/'NEV_PREFIX_CURRENT_PARTITION.json').write_text(json.dumps(dict(lo=lo,hi=hi,domain=f'{lo}<=length<={hi},index<length,observed<=index; all raw old words/product',setup='exact_vec/truncate')))
