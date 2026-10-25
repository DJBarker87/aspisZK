"""Reify each emitted Result call as a silent step; never replace an error arm."""
from pathlib import Path
import re
root=Path('docs/research/100bit-spend-path-20261013/lean')
def transform(body):
    ls=body.splitlines(); out=[]; i=0
    while i<len(ls):
        l=ls[i]; indent=len(l)-len(l.lstrip()); st=l.strip()
        if ('←' in l and st.startswith('let ')) or st.startswith(('ops.op','ops.trace','core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual')):
            j=i+1
            while j<len(ls) and ls[j].strip() and len(ls[j])-len(ls[j].lstrip())>indent:
                j+=1
            block='\n'.join(ls[i:j])
            if '←' in l:
                before,expr=block.split('←',1)
                block=before+'← call ('+expr.strip()+')'
            else:
                block=' '*indent+'call ('+block.strip()+')'
            out.append(block);i=j
        else:
            out.append(re.sub(r'\bok \(', 'pure (',l));i+=1
    return '\n'.join(out)
s=(root/'Port3_NativeFinishBody.lean').read_text();body=s.split('  := do\n',1)[1].split('\n\n\n#print')[0]
pre='''import T2Nat_Silent
import Port4D_FinishInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_FinishCode
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_Silent
variable {W : Type}

/-- Reification of the emitted parent, in the same source branch order.
Every primitive has its full Result; no success or comparison is assumed. -/
def parent (ops : Port3_NativeFinishBody.Ops W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit)) :
    Silent (core.result.Result Unit verifier.Error) := do
'''
post='''

theorem parent_erase (ops : Port3_NativeFinishBody.Ops W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit)) :
    erase (parent ops v p a obs) =
      Port3_NativeFinishBody.verifier.finish_relation ops v p a obs := by
  simp only [parent,Port3_NativeFinishBody.verifier.finish_relation,
    erase_bind,erase_call,erase_pure]
  repeat
    first
    | rfl
    | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro x hx)
    | (split <;> simp only [erase_bind,erase_call,erase_pure])

/-- Full Result and ordered log, for every error/failure branch as well as
success; the initial history is arbitrary and preserved byte for byte. -/
theorem parent_effects {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (ops : Port3_NativeFinishBody.Ops W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
    (before : CheckpointBytes5Effect.Log) :
    CheckpointBytes5Effect.run D hash (code (parent ops v p a obs)) before =
      (do let result ← Port3_NativeFinishBody.verifier.finish_relation ops v p a obs
          ok (result,before)) := by
  rw [ordered_log,parent_erase]

#print axioms parent_erase
#print axioms parent_effects
end AspisR1.T2Nat_FinishCode
end
'''
Path('lean/T2Nat_FinishCode.lean').write_text(pre+transform(body)+post)
