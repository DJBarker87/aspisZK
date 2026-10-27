import R1Z.PV_Src_RootHelper
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalAssociation
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! An explicit native external-call association, not a new trust item. -/
def Associated (external : ExternalLinear) : Prop := ∀ s,
  @poseidon2.external_linear_lazy external s = PV_Src_ExternalReference.run s

theorem dictionary (external : ExternalLinear) (h : Associated external) :
    external = PV_Src_ExternalReference.dictionary := by
  cases external with
  | mk call =>
    change ExternalLinear.mk call = ExternalLinear.mk PV_Src_ExternalReference.run
    congr 1
    funext s
    exact h s

#print axioms dictionary
end R1Z.PV_Src_ExternalAssociation
