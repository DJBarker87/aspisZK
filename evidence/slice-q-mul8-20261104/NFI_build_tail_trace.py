from pathlib import Path
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul7-20261104'
s=(P/'NFF_LoggedTail.lean').read_text();a=s.index('  let tail ←');b=s.index('\n\n\ntheorem replay',a);body=s[a:b]
# The following is a syntax-preserving lift: each original partial operation
# is executed once in source order. Only marks between original operations added.
lines=body.splitlines();commands=[]
for line in lines:
 if line.startswith('  let ') or line.startswith('  core.') or line.startswith('  ok '):commands.append(line)
 else:commands[-1]+='\n'+line
out=[]
for c in commands:
 if c.startswith('  let '):
  lhs,rhs=c.split(' ←',1);out.append(lhs+' ← lift ('+rhs.strip()+')')
  name=lhs[6:].strip()
  if name in ['tail','(r, tail1)','(r1, tail2)','(r2, tail3)']:
   receiver={'tail':'tail','(r, tail1)':'tail1','(r1, tail2)':'tail2','(r2, tail3)':'tail3'}[name]
   n={'tail':0,'(r, tail1)':1,'(r1, tail2)':2,'(r2, tail3)':3}[name]
   out.append(f'  mark (⟨{n},{receiver}⟩ : Cut input)')
 elif c.startswith('  core.'):out.append('  let _ ← lift ('+c.strip()+')')
 else:out.append(c.replace('  ok ','  pure '))
# q,g,slot are projections from the original input; never selected independently.
text='''import NFI_TraceResult
import NFI_InnerCut
import NFF_LoggedTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_TailTrace
open Aeneas Aeneas.Std Result NFI_TraceResult
abbrev Input := NFI_InnerCut.Input
structure Cut (input : Input) where
  ordinal : Nat
  receiver : FIo_Native.fast_pairing.EbyKDot

def run (oracle : NFF_ProductCall.Oracle) (input : Input) : M (Cut input) NEV_DotCarrier.NE := do
  let q := input.q
  let g := input.g
  let slot := input.slot
'''+ '\n'.join(out)+'''

theorem erased (oracle : NFF_ProductCall.Oracle) (input : Input) :
    (run oracle input).result=NFF_LoggedTail.run oracle input.q input.g input.slot := by
  have right {T : Type} (r : Result T) : (do let x ← r; ok x)=r := by cases r <;> rfl
  have split {A B C : Type} (f : A → B → C) (p : A × B) :
      (match p with | (a,b) => f a b)=f p.1 p.2 := by cases p; rfl
  simp only [run,NFF_LoggedTail.run,erase_bind,erase_lift,erase_mark,erase_pure,Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok,right,split]
  rfl

theorem emitted (oracle : NFF_ProductCall.Oracle) (law : NFF_ProductCall.Law oracle)
    (input : Input) :
    (run oracle input).result=NFE_NFA_SuffixFactor.tail input.q input.g input.slot := by
  rw [erased,NFF_LoggedTail.replay oracle law]

#print axioms erased
#print axioms emitted
end AspisR1.NFI_TailTrace
end
'''
(E/'NFI_TailTrace.lean').write_text(text)
(E/'NFI_TAIL_LIFT.json').write_text(__import__('json').dumps(dict(source=str(P/'NFF_LoggedTail.lean'),original_body=body,lifted_body='\n'.join(out),qualification='Each partial operation lifted exactly once; marks preserve rejected prefixes. Native physical installation requires the adjacent-window certificates.'),indent=2)+'\n')
