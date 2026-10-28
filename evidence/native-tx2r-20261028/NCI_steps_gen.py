from NCI_extend import extend,attrs
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
s=subprocess.check_output(['git','show','4bb3b3f5:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
b=s[s.index('fn accumulate_batched_with_node('):s.index('\npub fn polynomial(')]
statements=['basis[n+j]=basis[j].mul(node);','node=node.mul(node).double().sub(M31::ONE);']
for x in statements:assert b.count(x)==1,x
flush='*limb=(*limb&0x7fff_ffff)+(*limb>>31);'
assert flush in s
h='''
#[cfg(kani)] mod NCI_steps {
use super::*;
static mut LOG:[u32;3]=[0;3];
static mut CALLS:usize=0;
fn mul(x:M31,y:M31)->M31{let reply:u32=kani::any();kani::assume(reply<2147483647);unsafe{LOG=[x.0,y.0,reply];CALLS+=1;}M31(reply)}
'''
for name in ['basis','node','flush']:
 for wrong in [False,True]:
  h+=attrs+('#[kani::stub(aspis_core::field::M31::mul,mul)]\n' if name!='flush' else '')+f'fn {name}_{"wrong" if wrong else "ok"}(){{\n'
  op='!=' if wrong else '=='
  if name=='basis':
   h+='let mut basis=['+','.join(['M31(kani::any())']*256)+'];\n'
   h+='''let stage:usize=kani::any();kani::assume(stage<6);let n=1usize<<stage;let j:usize=kani::any();kani::assume(j<n);
let node=M31(kani::any());kani::assume(node.0<2147483647&&basis[j].0<2147483647);
let k:usize=kani::any();kani::assume(k<256&&k!=n+j);let before=basis[k];let left=basis[j];
'''+statements[0]+'\n'
   h+=f'''let log=unsafe{{LOG}};assert!(unsafe{{CALLS}}==1&&log[0]==left.0&&log[1]==node.0);
assert!(basis[k]==before);assert!(basis[n+j].0{op}log[2]);assert!(basis[n+j].0<2147483647);
'''
  if name=='node':
   h+='let mut node=M31(kani::any());kani::assume(node.0<2147483647);let before=node;\n'+statements[1]+'\n'
   h+=f'''let log=unsafe{{LOG}};assert!(unsafe{{CALLS}}==1&&log[0]==before.0&&log[1]==before.0);
let sum=(log[2] as u64)*2;let doubled=if sum>=2147483647{{sum-2147483647}}else{{sum}};
let expected=if doubled==0{{2147483646}}else{{doubled-1}};
assert!((node.0 as u64){op}expected);assert!(node.0<2147483647);
'''
  if name=='flush':
   h+='let mut row:[u64;4]=kani::any();let j:usize=kani::any();kani::assume(j<4);let k:usize=kani::any();kani::assume(k<4&&k!=j);let before=row[j];let other=row[k];let limb=&mut row[j];\n'+flush+'\n'
   h+=f'assert!(row[k]==other);assert!(row[j]{op}before%2147483648+before/2147483648);assert!(row[j]<17179869184);\n'
  h+='}\n'
h+='}\n'
extend('NCI_steps.patch',h)
(E/'NCI_STEP_SOURCE.json').write_text(json.dumps({'frozen':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','scope':'lexically exact single statements; not whole native caller','accumulate_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'statements':statements+[flush]},indent=2)+'\n')
