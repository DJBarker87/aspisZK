from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
words=lambda i:','.join('word(&bytes,'+str(i+4*j)+')' for j in range(4))
s='''use super::*;
use aspis_core::field::{M31,CM31};
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn word(bytes:&[u8],at:usize)->u32{u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]])}
fn kw(q:K)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn check(){let bytes:[u8;160]=kani::any();
 let good='''+'&&'.join('word(&bytes,'+str(4*i)+')<2147483647' for i in range(40))+''';
 let result=read_checkpoint_semantic_alpha(&bytes,0);
 assert_eq!(result.is_ok(),good^cfg!(NJC_invert));
 match result{Ok((out,at))=>{assert_eq!(at,160);
'''+''.join('assert_eq!(kw(out['+str(i)+']),['+words(16*i)+']);\n' for i in range(10))+'''},Err(error)=>assert_eq!(error,Error::Checkpoint)}
}
'''
for suffix in ['','_renamed']:
 s+='''#[kani::proof]
#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn semantic'''+suffix+'(){check();}\n'
(E/'NJC_semantic.rs.txt').write_text(s)
x=json.loads((E/'NJC_NATIVE_INPUTS.json').read_text());path='crates/aspis-r1-cost-probe/src/verifier.rs';assert 'mod NJC_semantic;' not in x[path]
x[path]+='\n#[cfg(kani)]\n#[path="NJC_semantic.rs"]\nmod NJC_semantic;\n';x['crates/aspis-r1-cost-probe/src/NJC_semantic.rs']=s
(E/'NJC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
pins=json.loads((E/'NJC_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NJC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch='';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for n,t in x.items():
 z=subprocess.run(['git','show',rev+':'+n],capture_output=True,text=True);old=z.stdout if z.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJC_native.patch').write_text(patch)
