from pathlib import Path
import re
L=Path('lean');types=(L/'NCX_Reference/Types.lean').read_text()
s='''import NCX_Carrier
import NCV_ArrayFrame
set_option autoImplicit false
namespace NCX_Observations
open Aeneas Aeneas.Std Result
inductive Observation where
 | byte : U8 → Observation
 | word : U64 → Observation
 | status : NCX_Reference.VerifierEntryStatusV1 → Observation

def registry (v : NCX_Reference.VerifierRegistryV2) (field j : Nat) : Observation :=
'''
for key,name in [('registry','VerifierRegistryV2'),('entry','VerifierRegistryEntryV2')]:
 fs=re.findall(r'^  (\w+) : (.+)',types.split('structure '+name+' where')[1].split('/--')[0],re.M)
 if key=='entry':s+='\ndef entry (v : NCX_Reference.VerifierRegistryEntryV2) (field j : Nat) : Observation :=\n'
 s+='  match field with\n'
 for i,(f,t) in enumerate(fs):
  expr='.status v.status' if f=='status' else '.byte (NCV_ArrayFrame.coord v.'+f+' j)' if 'Array' in t else '.word v.'+f if 'U64' in t else '.byte v.'+f
  s+=f'  | {i} => {expr}\n'
 s+='  | _ => .byte 0#u8\n'
 s+=f'''\n/-- Full record equality follows from arbitrary field and byte observations. -/
theorem {key}_injective (a b : NCX_Reference.{name})
    (same : ∀ field j, field<{len(fs)} → j<32 → {key} a field j={key} b field j) : a=b := by
'''
 for i,(f,t) in enumerate(fs):
  s+=f'  have e_{f} : a.{f}=b.{f} := by\n'
  if 'Array' in t:
   s+='    apply NCV_ArrayFrame.whole\n    intro j hj _\n'
   s+=f'    have h:=same {i} j (by omega) hj\n    exact Observation.byte.inj h\n'
  else:
   obs='status' if f=='status' else 'word' if 'U64' in t else 'byte'
   s+=f'    exact Observation.{obs}.inj (same {i} 0 (by omega) (by omega))\n'
 s+='  cases a;cases b\n  '+ ';'.join('cases e_'+f for f,t in fs)+'\n  rfl\n'
 s+=f'#print axioms {key}_injective\n'
s+='end NCX_Observations\n';(L/'NCX_Observations.lean').write_text(s)
