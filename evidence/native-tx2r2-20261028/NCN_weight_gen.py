from NCN_extend import E,extend,attrs
import subprocess,json,hashlib
s=subprocess.check_output(['git','show','4bb3b3f5:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
body=s[s.index('        let mut reader=Reader{bytes,at};',s.index('fn read_checkpoint_weights')):s.index('\n    }',s.index('fn read_checkpoint_weights'))]
assert body=='''        let mut reader=Reader{bytes,at};
        let value=reader.k()?;
        at=reader.at;
        *out=value;'''
h='''
#[cfg(kani)] mod NCN_weights {
use super::*;
static mut CALLS:usize=0;
static mut REPLY:Option<K>=None;
fn iteration(bytes:&[u8],mut at:usize,out:&mut K)->Result<usize,Error>{
unsafe{CALLS+=1;}
let mut reader=Reader{bytes,at};
let value=reader.k()?;
unsafe{REPLY=Some(value);}
at=reader.at;
*out=value;
Ok(at)
}
'''
q=[]
for kind in ['cursor','reply','frame','error','iterator']:
 for neg in [False,True]:
  name=kind+('_wrong' if neg else '_ok')
  h+=attrs+'#[kani::stub_verified(Reader::k)]\n'+f'fn {name}(){{\n'
  h+='let bytes:[u8;1768]=kani::any();let mut weights=['+','.join(['K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}']*64)+'];\n'
  h+='''let i:usize=kani::any();let k:usize=kani::any();kani::assume(i<64&&k<64&&k!=i);
let start=712+16*i;let before=weights[i];let frame=weights[k];
let result;let remaining;
{let mut iter=weights[i..].iter_mut();let out=iter.next().unwrap();result=iteration(&bytes,start,out);remaining=iter.len();}
assert!(unsafe{CALLS}==1);
'''
  op='!=' if neg else '=='
  if kind=='cursor':h+=f'if let Ok(at)=result{{assert!(at{op}start+16);}}\n'
  if kind=='reply':h+=f'if result.is_ok(){{assert!(Some(weights[i]){op}unsafe{{REPLY}});}}\n'
  if kind=='frame':h+=f'assert!(weights[k]{op}frame);\n'
  if kind=='error':h+=f'if result.is_err(){{assert!(weights[i]{op}before);assert!(unsafe{{REPLY}}.is_none());}}\n'
  if kind=='iterator':h+=f'assert!(remaining{op}63-i);\n'
  h+='}\n';q.append(dict(harness='verifier::NCN_weights::'+name,negative=neg))
h+='}\n';extend('NCN_weights.patch',h)
for i,x in enumerate(q,31):x.update(attempt=f'NCN_K{i:03}',patch='NCN_weights.patch')
(E/'NCN_weight_queue.json').write_text(json.dumps(q,indent=2)+'\n')
(E/'NCN_WEIGHT_SOURCE.json').write_text(json.dumps(dict(frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',body=body,sha256=hashlib.sha256(body.encode()).hexdigest(),instrumentation='CALLS before construction and REPLY after the successful k return; erasure restores exact body',scope='one arbitrary suffix iterator step on a valid64-cell borrowed array; Vec allocation/ownership lower boundary retained'),indent=2)+'\n')
