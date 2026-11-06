from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
s='''use super::*;
use aspis_core::field::{M31,CM31};
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn k(x:[u32;4])->K{K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn kw(q:K)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn e(x:[u32;8])->E{E::new(k([x[0],x[1],x[2],x[3]]),k([x[4],x[5],x[6],x[7]]))}
fn construct(weights:Vec<K>,rhs:E,power:K,next:u8,at:usize,end:usize)->Result<Accumulator,Error>{
 if at!=end{return Err(Error::Checkpoint);}
 Ok(Accumulator{weights,rhs,power,next:next as usize})
}
fn check(){
 let before:[[u32;4];64]=kani::any();let values:[K;64]=core::array::from_fn(|i|k(before[i]));let weights=Vec::from(values);let addr=weights.as_ptr();let cap=weights.capacity();
 let rhs=e(kani::any());let power=k(kani::any());let next:u8=kani::any();let at:usize=kani::any();let end:usize=kani::any();let j:usize=kani::any();kani::assume(j<64);
 let result=construct(weights,rhs,power,next,at,end);assert_eq!(result.is_ok(),at==end);
 match result{Err(error)=>assert_eq!(error,Error::Checkpoint),Ok(mut a)=>{
  if cfg!(NJC_invert){a.weights[j].c0.a.0^=1;}
  if cfg!(NJC_bad_alloc){let other=Vec::from(values);a.weights=other;}
  assert_eq!(a.weights.as_ptr(),addr);assert_eq!(a.weights.capacity(),cap);assert_eq!(a.weights.len(),64);assert_eq!(kw(a.weights[j]),before[j]);assert_eq!(a.rhs,rhs);assert_eq!(a.power,power);assert_eq!(a.next,next as usize);
 }}
}
'''
for suffix in ['','_renamed']:
 s+='''#[kani::proof]
#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn accumulator'''+suffix+'(){check();}\n'
(E/'NJC_vec.rs.txt').write_text(s);x=json.loads((E/'NJC_NATIVE_INPUTS.json').read_text());p='crates/aspis-r1-cost-probe/src/verifier.rs';assert 'mod NJC_vec;' not in x[p];x[p]+='\n#[cfg(kani)]\n#[path="NJC_vec.rs"]\nmod NJC_vec;\n';x['crates/aspis-r1-cost-probe/src/NJC_vec.rs']=s
(E/'NJC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NJC_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NJC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch='';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for n,t in x.items():
 z=subprocess.run(['git','show',rev+':'+n],capture_output=True,text=True);old=z.stdout if z.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJC_native.patch').write_text(patch)
