from pathlib import Path
import difflib,json
E=Path(__file__).resolve().parent
src=(E/'NCN_verifier_before.txt').read_text()
attrs='''#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,NCI_kmx::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,NCI_kmx::KMX_copy_from_slice)]
'''
h='\n#[cfg(kani)] mod NCN_raw {\nuse super::*;\n'
queue=[]
for n in [1,4,16,32]:
 for neg in [False,True]:
  name=f'raw{n}_'+('wrong' if neg else 'ok')
  h+=attrs+f'''fn {name}(){{
let bytes:[u8;1768]=kani::any();let start:usize=kani::any();kani::assume(start<=1768-{n});
let j:usize=kani::any();kani::assume(j<{n});let k:usize=kani::any();kani::assume(k<1768);
let want=bytes[start+j];let frame=bytes[k];let ptr=bytes.as_ptr();
let mut r=Reader{{bytes:&bytes,at:start}};let out=r.raw::<{n}>();
assert!(out[j]{'!=' if neg else '=='}want);assert!(r.at==start+{n});assert!(r.bytes.as_ptr()==ptr);assert!(r.bytes.len()==1768);assert!(r.bytes[k]==frame);
}}\n'''
  queue.append(dict(attempt=f'NCN_K{len(queue)+1:03}',harness='verifier::NCN_raw::'+name,negative=neg,patch='NCN_raw.patch'))
h+='}\n'
patch=''.join(difflib.unified_diff(src.splitlines(True),(src+h).splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/verifier.rs',tofile='b/crates/aspis-r1-cost-probe/src/verifier.rs'))
(E/'NCN_raw.patch').write_text(patch)
(E/'NCN_raw_queue.json').write_text(json.dumps(queue,indent=2)+'\n')
