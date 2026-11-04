import NFG_InverseRef.Funs
import NFG_ResultCongr
set_option autoImplicit false
namespace NFG_QmInvCuts
open Aeneas Aeneas.Std Result NFG_InverseRef
/-- The same child Option must be Some; a separate successful child is not a premise. -/
theorem returned (x out : field.QM31) (accepted : field.QM31.inv x=ok out) :
 field.QM31.try_inv x=ok (some out) := by
 unfold field.QM31.inv at accepted
 obtain ⟨reply,child,accepted⟩ := NFG_ResultCongr.bind_success _ _ _ accepted
 cases reply with
 | none => cases accepted
 | some actual =>
  have same : actual=out := Result.ok.inj accepted
  cases same
  exact child
#print axioms returned
end NFG_QmInvCuts
