import NLV_RowSpec094
set_option autoImplicit false
namespace AspisR1.NMG_AbortGap094
open Aeneas Aeneas.Std Result
/-- This is only the ReturnedOwnership field, not a counterexample to the
entire Invocation relation or to deployed code. -/
theorem fail_unconstrained (out : NLV_Interface.Observation094) (e : Error)
 (raw : out.raw=.fail e) : NLV_Interface.ReturnedOwnership out := by
 unfold NLV_Interface.ReturnedOwnership
 rw [raw]
 trivial
theorem div_unconstrained (out : NLV_Interface.Observation094)
 (raw : out.raw=.div) : NLV_Interface.ReturnedOwnership out := by
 unfold NLV_Interface.ReturnedOwnership
 rw [raw]
 trivial
#print axioms fail_unconstrained
#print axioms div_unconstrained
end AspisR1.NMG_AbortGap094
