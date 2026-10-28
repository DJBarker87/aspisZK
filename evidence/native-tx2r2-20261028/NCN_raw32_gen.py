from NCN_extend import extend,attrs,E
import json
h='\n#[cfg(kani)] mod NCN_raw32 {\nuse super::*;\n';qs=[]
for group,base,count in [('prefix',80,7),('tail',632,2)]:
 for neg in [False,True]:
  name=group+('_wrong' if neg else '_ok')
  h+=attrs+f'''fn {name}(){{
let bytes:[u8;1768]=kani::any();let slot:usize=kani::any();kani::assume(slot<{count});let start={base}+32*slot;
let j:usize=kani::any();kani::assume(j<32);let k:usize=kani::any();kani::assume(k<1768);
let want=bytes[start+j];let frame=bytes[k];let ptr=bytes.as_ptr();
let mut r=Reader{{bytes:&bytes,at:start}};let out=r.raw::<32>();
assert!(out[j]{'!=' if neg else '=='}want);assert!(r.at==start+32);assert!(r.bytes.as_ptr()==ptr);assert!(r.bytes.len()==1768);assert!(r.bytes[k]==frame);
}}\n'''
  qs.append(dict(harness='verifier::NCN_raw32::'+name,negative=neg))
h+='}\n';extend('NCN_raw32.patch',h)
for i,q in enumerate(qs,16):q.update(attempt=f'NCN_K{i:03}',patch='NCN_raw32.patch')
(E/'NCN_raw32_queue.json').write_text(json.dumps(qs,indent=2)+'\n')
