import NLV_RowSpec087
set_option autoImplicit false
namespace AspisR1.NMG_AbortGap087
open Aeneas Aeneas.Std Result
/-- Actual draft imposes no abort ownership or cleanup predicate. -/
theorem fail_unconstrained (after : NLV_Resource087.State) (e : Error) :
 NLV_Resource087.Returned (.fail e) after := trivial
theorem div_unconstrained (after : NLV_Resource087.State) :
 NLV_Resource087.Returned .div after := trivial
#print axioms fail_unconstrained
#print axioms div_unconstrained
end AspisR1.NMG_AbortGap087
