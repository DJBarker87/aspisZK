import NFG_InverseNone
import NFG_QmInvCuts
set_option autoImplicit false
namespace NFG_InversePanic
open Aeneas Aeneas.Std Result NFG_InverseRef
/-- None is preserved as expect's panic Result; it is never silently discarded. -/
theorem zero (x : field.QM31) (test : field.QM31.is_zero x=ok true) :
 field.QM31.inv x=fail .panic := by
 rw [field.QM31.inv,NFG_TryInvCuts.zero x test]
 rfl
/-- Any returned inverse is associated with the SAME false zero test. -/
theorem returned (x out : field.QM31) (run : field.QM31.inv x=ok out) :
 field.QM31.is_zero x=ok false :=
 (NFG_TryInvCuts.accepted x out (NFG_QmInvCuts.returned x out run)).1
#print axioms zero
#print axioms returned
end NFG_InversePanic
