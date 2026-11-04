import NFB_TailDefs
import NFB_ResultIdentity
import NFG_ResultCongr
set_option autoImplicit false
noncomputable section
namespace NFG_TailProgram
open NFB_TailProgram
open Aeneas Aeneas.Std Result AspisR1
/-- Symbolic bind reassociation only; every partial Result is preserved. -/
theorem association (q : Array U8 608#usize) (g : Coeff) (slot : Usize) :
 NFA_SuffixFactor.tail q g slot=run q g slot := by
 simp only [NFA_SuffixFactor.tail,run,first,later,push,NFA_TailQM.read,
  uncurry,bind_assoc_eq,bind_tc_ok,NFB_ResultIdentity.right,NFB_BindPair.split]
 repeat' first
 | (with_reducible rfl)
 | (apply NFG_ResultCongr.pair_congr; intro a b)
 | (apply NFG_ResultCongr.bind_congr; intro x)
 | (with_reducible rfl)
#print axioms association
end NFG_TailProgram
end
