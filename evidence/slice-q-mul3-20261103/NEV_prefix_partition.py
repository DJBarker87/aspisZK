"""Capacity partitions of a native append; union needed before any closure."""
from pathlib import Path
import json,difflib,sys
E=Path(__file__).resolve().parent
lo,hi=map(int,sys.argv[1:]);assert 1<=lo<=hi<=110
x=json.loads((E/'NEV_PAYLOAD.json').read_text());n='crates/aspis-r1-cost-probe/src/NEV_prefix_step.rs'
s=x[n].split('// Arbitrary valid prestate, built at fixed offsets.')[0]
s+=f'''// Partition {lo}..={hi}. Every length/index/old value in this interval is arbitrary.
#[kani::proof] #[kani::unwind(114)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::NEV_copy::KMX_realloc)]
fn prefix_push_fixed_offsets() {{
 let length:usize=kani::any();let index:usize=kani::any();
 kani::assume({lo}<=length && length<={hi} && index<length);
 let mut before:Vec<M31>=Vec::with_capacity(length);
 assert_eq!(before.capacity(),length);
 let initialized=before.as_mut_ptr();
'''
for i in range(hi):s+=f' if {i}<index {{unsafe {{initialized.add({i}).write(M31(kani::any()));}}}}\n'
s+='''
 unsafe {before.set_len(index);}
 let observed:usize=kani::any();kani::assume(observed<=index);
 let product=M31(kani::any());let old=if observed<index{before[observed].0}else{product.0};
 let pointer=before.as_ptr();
 before.push(product);
 let after=unsafe {before.as_ptr().add(observed).read()}.0;
 assert_eq!(after,if cfg!(NEV_wrong_fixed_offsets){old^1}else{old});
 assert!(before.len()==index+1 && before.capacity()==length && before.as_ptr()==pointer);
}
'''
x[n]=s;(E/'NEV_PREFIX_NATIVE.rs').write_text(s);(E/'NEV_PAYLOAD.json').write_text(json.dumps(x))
frozen=json.loads((E/'NEV_FROZEN.json').read_text());patch=''
for n,t in x.items():
 if n.endswith('.lean'):continue
 patch+=''.join(difflib.unified_diff(frozen.get(n,'').splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NEV_native.patch').write_text(patch)
(E/'NEV_PREFIX_CURRENT_PARTITION.json').write_text(json.dumps(dict(lo=lo,hi=hi,domain=f'{lo}<=length<={hi},index<length,observed<=index; all raw old words/product')))
