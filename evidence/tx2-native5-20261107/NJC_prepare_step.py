from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
s='''use super::*;
use aspis_core::field::{M31,CM31};
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn word(bytes:&[u8],at:usize)->u32{u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]])}
fn make(x:[u32;4])->K{K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn words(q:K)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
// One literal frozen read_checkpoint_weights iteration, on an arbitrary
// pre-iterator suffix. The parent establishes suffix=remaining SAME Vec.
fn step(bytes:&[u8],at:usize,remaining:&mut[K])->Result<usize,Error>{
 let mut iter=remaining.iter_mut();
 match iter.next(){None=>Ok(at),Some(out)=>{
  let mut reader=Reader{bytes,at};let value=reader.k()?;
  let at=reader.at;*out=value;Ok(at)
 }}
}
fn check(){
 let bytes:[u8;16]=kani::any();let before:[[u32;4];64]=kani::any();
 let mut values:[K;64]=core::array::from_fn(|i|make(before[i]));
 let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<64&&j<64);
 let expected=[word(&bytes,0),word(&bytes,4),word(&bytes,8),word(&bytes,12)];
 let good=expected[0]<2147483647&&expected[1]<2147483647&&expected[2]<2147483647&&expected[3]<2147483647;
 let result=step(&bytes,0,&mut values[i..]);
 assert_eq!(result.is_ok(),good^cfg!(NJC_invert));
 match result{Ok(at)=>{assert_eq!(at,16);assert_eq!(words(values[j]),if j==i{expected}else{before[j]});},Err(error)=>{assert_eq!(error,Error::Checkpoint);assert_eq!(words(values[j]),before[j]);}}
}
'''
for suffix in ['','_renamed']:
 s+='''#[kani::proof]
#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn weight_step'''+suffix+'(){check();}\n'
(E/'NJC_weight_step.rs.txt').write_text(s)
x=json.loads((E/'NJC_NATIVE_INPUTS.json').read_text());path='crates/aspis-r1-cost-probe/src/verifier.rs';assert 'mod NJC_weight_step;' not in x[path]
x[path]+='\n#[cfg(kani)]\n#[path="NJC_weight_step.rs"]\nmod NJC_weight_step;\n';x['crates/aspis-r1-cost-probe/src/NJC_weight_step.rs']=s
(E/'NJC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
pins=json.loads((E/'NJC_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NJC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch='';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for n,t in x.items():
 z=subprocess.run(['git','show',rev+':'+n],capture_output=True,text=True);old=z.stdout if z.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJC_native.patch').write_text(patch)
