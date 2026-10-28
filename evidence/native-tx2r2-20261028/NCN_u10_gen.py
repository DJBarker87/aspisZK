from NCN_extend import E,extend,attrs
import json,subprocess,hashlib
s=subprocess.check_output(['git','show','4bb3b3f5:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
init='''            let w=weights[index];
            raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
            index+=1;'''
assert init in s
h='''
#[cfg(kani)] mod NCN_u10 {
use super::*;
fn reduce(x:u64)->M31{let z:u32=kani::any();kani::assume(z as u64==x%2147483647);M31(z)}
fn init_iteration(weights:&[K],raw:&mut[[u64;4]],mut index:usize)->usize{
'''+init+'''
index
}
'''
q=[]
for kind in ['vec_row','value','new','finish','cadence']:
 for neg in [False,True]:
  name=kind+('_wrong' if neg else '_ok');op='!=' if neg else '=='
  h+=attrs+('#[kani::stub(aspis_core::field::M31::reduce_u64,reduce)]\n' if kind in ['value','finish'] else '')+f'fn {name}(){{\n'
  if kind=='cadence':
   h+='let terms:usize=kani::any();let flush=terms&3==3;\n'+f'assert!(flush{op}(terms%4==3));\n'
  elif kind in ['vec_row','value','finish']:
   h+='''let rows:[[u64;4];64]=kani::any();let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(i<64&&j<4&&k<64&&k!=i);
let source=rows[i][j];let frame=rows[k][j];let terms:usize=kani::any();
let state=BatchedWeights{raw:Vec::from(rows),terms};let ptr=state.raw.as_ptr();
'''
   if kind=='vec_row':h+=f'''let row=state.raw[i];assert!(row[j]{op}source);assert!(state.raw.len()==64&&state.raw.as_ptr()==ptr&&state.terms==terms);assert!(state.raw[k][j]==frame);\n'''
   if kind=='value':h+=f'''let value=state.value(i);let limbs=[value.c0.a.0,value.c0.b.0,value.c1.a.0,value.c1.b.0];assert!((limbs[j] as u64){op}source%2147483647);assert!(state.raw[i][j]==source&&state.raw[k][j]==frame&&state.terms==terms);\n'''
   if kind=='finish':
    h+='''let mut weights:[K;64]=kani::any();let old=weights[k];let count;{
let mut iter=weights[i..].iter_mut().enumerate();let (local,w)=iter.next().unwrap();count=local+i;*w=state.value(count);}
let value=weights[i];let limbs=[value.c0.a.0,value.c0.b.0,value.c1.a.0,value.c1.b.0];
'''+f'''assert!((limbs[j] as u64){op}source%2147483647);assert!(count==i&&weights[k]==old&&state.raw[k][j]==frame&&state.terms==terms);\n'''
  elif kind=='new':
   h+='''let weights:[K;64]=kani::any();let mut raw:[[u64;4];64]=kani::any();let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(i<64&&j<4&&k<64&&k!=i);let frame=raw[k];let w=weights[i];let expected=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];let next=init_iteration(&weights,&mut raw,i);
'''+f'assert!(raw[i][j]{op}expected[j]);assert!(next==i+1&&raw[k]==frame);\n'
  h+='}\n';q.append(dict(harness='verifier::NCN_u10::'+name,negative=neg))
h+='}\n';extend('NCN_u10.patch',h)
for i,x in enumerate(q,55):x.update(attempt=f'NCN_K{i:03}',patch='NCN_u10.patch')
(E/'NCN_u10_queue.json').write_text(json.dumps(q,indent=2)+'\n')
(E/'NCN_U10_SOURCE.json').write_text(json.dumps(dict(init=init,init_sha256=hashlib.sha256(init.encode()).hexdigest(),finish='one native suffix iterator next/write; global index recovered as local+i, full Vec ownership retained',reducer_pair='AspisR1.NCI_PendingReducer.reducer_ok on every U64; copied exact NCI reducer spec; no multiplication'),indent=2)+'\n')
