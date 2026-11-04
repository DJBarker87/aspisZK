import NFB_TailDefs
import NFB_ResultIdentity
import NEW_GeometryRawBody
set_option autoImplicit false
noncomputable section
namespace NFB_TailProgram
open Aeneas Aeneas.Std Result AspisR1
/-- Symbolic bind reassociation only; every partial Result is preserved. -/
theorem association (q : Array U8 608#usize) (g : Coeff) (slot : Usize) :
 NFA_SuffixFactor.tail q g slot=run q g slot := by
 simp only [NFA_SuffixFactor.tail,run,first,later,push,NFA_TailQM.read,
  uncurry,bind_assoc_eq,bind_tc_ok,NFB_ResultIdentity.right,NFB_BindPair.split]
 repeat' first
 | (apply NEW_GeometryRawBody.bind_congr
    intro x
    simp only [NFB_BindPair.split,uncurry,bind_assoc_eq,bind_tc_ok,NFB_ResultIdentity.right])
 | (with_reducible rfl)
#print axioms association
end NFB_TailProgram
end
