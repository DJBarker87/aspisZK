from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
struct Contains<'a>{queries:&'a[u32;22],i:usize,answer:bool,calls:usize}
impl Contains<'_>{fn contains(&mut self,prefix:&[u32],q:&u32)->bool{
 assert_eq!(prefix.as_ptr(),self.queries.as_ptr());assert_eq!(prefix.len(),self.i);assert_eq!(*q,self.queries[self.i]);self.calls+=1;self.answer
}}
// Literal one entered outer iteration; contains is the entered child cut.
fn step(queries:&[u32;22],i:usize,log:&mut Contains)->Result<usize,Error>{
 let q=queries[i];
 if q>=1<<18||log.contains(&queries[..i],&q){return Err(Error::Checkpoint);}
 Ok(i+1)
}
fn check(){let queries:[u32;22]=kani::any();let i:usize=kani::any();kani::assume(i<22);let answer:bool=kani::any();let mut log=Contains{queries:&queries,i,answer,calls:0};
 let result=step(&queries,i,&mut log);let bad=queries[i]>=262144||answer;
 assert_eq!(result.is_err(),bad^cfg!(NJC_invert));
 match result{Ok(next)=>assert_eq!(next,i+1),Err(e)=>assert_eq!(e,Error::Checkpoint)}
 assert_eq!(log.calls,if queries[i]>=262144{0}else{1});
}
'''
for suffix in ['','_renamed']:
 s+='''#[kani::proof]
#[kani::unwind(26)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn validate_step'''+suffix+'(){check();}\n'
(E/'NJC_validate.rs.txt').write_text(s)
x=json.loads((E/'NJC_NATIVE_INPUTS.json').read_text());p='crates/aspis-r1-cost-probe/src/verifier.rs';assert 'mod NJC_validate;' not in x[p];x[p]+='\n#[cfg(kani)]\n#[path="NJC_validate.rs"]\nmod NJC_validate;\n';x['crates/aspis-r1-cost-probe/src/NJC_validate.rs']=s
(E/'NJC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NJC_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NJC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch='';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for n,t in x.items():
 z=subprocess.run(['git','show',rev+':'+n],capture_output=True,text=True);old=z.stdout if z.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJC_native.patch').write_text(patch)
