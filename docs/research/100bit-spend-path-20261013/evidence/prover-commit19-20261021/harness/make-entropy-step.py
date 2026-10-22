"""Copy one production loop body exactly, changing only Option return framing.
The generator is not changed. This is a source-slice P6 boundary, not a Kani
proof of all sixteen iterations at once; Lean composes the step law.
"""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent.parent
p=Path('crates/aspis-prover/src/state_only_entropy.rs');s=p.read_text()
a=s.index('            let mut bytes = Zeroizing::new([0u8; 96]);',s.index('    pub fn generate()'))
b=s.index('\n        }\n        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)',a)
body=s[a:b]
assert body.count('return Ok(Self {')==1 and body.count('                });')==1
step=body.replace('return Ok(Self {','return Ok(Some(Self {').replace('                });','                }));')
step='\n#[cfg(any(kani,aeneas_ref))]\nimpl StateOnlyAttemptSecrets {\nfn entropy_draw_step19()->Result<Option<Self>,StateOnlyAttemptEntropyError> {\n'+step+'\n    Ok(None)\n}\n}\n'
raw=['kani::any()']*96
harness='''
#[cfg(kani)]
mod entropy19 {
 use super::*;
 static mut CALLS:usize=0;
 static mut RAW:[u8;96]=[0;96];
 fn draw(dest:&mut [u8])->Result<(),getrandom::Error> {
  assert_eq!(dest.len(),96);
  unsafe {CALLS+=1;
'''+''.join(f'  dest[{i}]=RAW[{i}];\n' for i in range(96))+''' }
  Ok(())
 }
'''
for j in range(3):
 harness+=''' #[kani::proof]
 #[kani::unwind(98)]
 #[kani::stub(getrandom::fill,draw)]
 fn reject_block_'''+str(j)+'''() {
  let raw:[u8;96]=['''+','.join(raw)+'''];
'''+''.join(f'  kani::assume(raw[{i}]==0);\n' for i in range(32*j,32*(j+1)))+'''  unsafe {RAW=raw;CALLS=0;}
  let actual=StateOnlyAttemptSecrets::entropy_draw_step19();
  assert!(matches!(actual,Ok(None)));
  assert_eq!(unsafe{CALLS},1);
 }
'''
harness+='}\n'
(E/'entropy-step19.rs').write_text(step)
(E/'harness/entropy19.rs').write_text(harness)
(E/'entropy-step-binding.json').write_text(json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(s.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),step_sha256=hashlib.sha256(step.encode()).hexdigest(),replacements=[['return Ok(Self {','return Ok(Some(Self {'],['                });','                }));']],boundary='Verbatim one-draw body, only Option return framing; source for-loop composition remains the P6 control-flow boundary.'),indent=2)+'\n')
(E/'harness/entropy19.instrumentation.rs').write_text(step+harness)
