import NJQ_Identity
import NJI_PolicyTotal
import NJI_MasterModel
set_option autoImplicit false
noncomputable section
namespace NJQ_ChildTotal
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

/-- This is a proved totality fact about the fixed model, never a caller hypothesis. -/
theorem identity_total (b : Slice U8) : ∃ r, NJQ_Identity.model b=ok r := by
 unfold NJQ_Identity.model
 repeat' first | split | exact ⟨_,rfl⟩

def identity (b : Slice U8) := Classical.choose (identity_total b)
theorem identity_value (b : Slice U8) : NJQ_Identity.model b=ok (identity b) :=
 Classical.choose_spec (identity_total b)

theorem policy_total (b : Slice U8) : ∃ r, NJI_PolicyParser.body b=ok r := by
 unfold NJI_PolicyParser.body
 repeat' first | exact ⟨_,rfl⟩ | split | (simp only [NJI_PolicyPort.validator_value,bind_tc_ok])

def policy (b : Slice U8) := Classical.choose (policy_total b)
theorem policy_value (b : Slice U8) : NJI_PolicyParser.body b=ok (policy b) :=
 Classical.choose_spec (policy_total b)

theorem master_total (m : NJI_MasterModel.M) : ∃ r, NJI_MasterModel.model m=ok r := by
 unfold NJI_MasterModel.model
 repeat' first | exact ⟨_,rfl⟩ | split | (simp only [NJI_PolicyPort.validator_value,bind_tc_ok])

def master (m : NJI_MasterModel.M) := Classical.choose (master_total m)
theorem master_value (m : NJI_MasterModel.M) : NJI_MasterModel.model m=ok (master m) :=
 Classical.choose_spec (master_total m)

#print axioms master_total
#print axioms master_value
#print axioms identity_total
#print axioms identity_value
#print axioms policy_total
#print axioms policy_value
end NJQ_ChildTotal
