import NFB_TailDefs
import NFB_ResultIdentity
set_option autoImplicit false
noncomputable section
namespace NFB_TailProgram
open Aeneas Aeneas.Std Result AspisR1
/-- Symbolic bind reassociation only; every partial Result is preserved. -/
theorem association (q : Array U8 608#usize) (g : Coeff) (slot : Usize) :
 NFA_SuffixFactor.tail q g slot=run q g slot := by
 simp only [NFA_SuffixFactor.tail,run,first,later,push,NFA_TailQM.read,
  NFB_ResultIdentity.pair_bind,uncurry,bind_assoc_eq,bind_tc_ok,NFB_ResultIdentity.right]
 repeat' first
 | (with_reducible rfl)
 | (apply (bind_eq_iff _ _ _).mpr
    intro x hx
    cases x
    simp only [uncurry,bind_assoc_eq,bind_tc_ok,NFB_ResultIdentity.right])
#print axioms association
end NFB_TailProgram
end
