import R1Z.ProverRw19AuditValue
import R1Z.ProverRwBodyDataCriterion
import R1Z.PV_RW_DataProduct
set_option autoImplicit false
namespace R1Z.ProverRw19AuditData
open Aeneas Aeneas.Std Result ProverRwFull ProverRw19AuditValue ProverRwBodyDataCriterion

abbrev ByteStatus := core.result.Result (alloc.vec.Vec U8) verifier.Error

-- A codec for a mathematical byte-result, not a whole-prover model. The
-- argument must eventually come from the independent mathematical model;
-- choosing it as the actual source's byte observation would prove nothing.
def attachAudit : Result ByteStatus → Result Status
  | .ok (.Ok bytes) => .ok (.Ok (bytes, canonical))
  | .ok (.Err error) => .ok (.Err error)
  | .fail error => .fail error
  | .div => .div

theorem bytes (modelBytes : Result ByteStatus) :
    PV_RW_DataProduct.observe PV_RW_DataProduct.first (attachAudit modelBytes) = modelBytes := by
  cases modelBytes with
  | ok status => cases status <;> rfl
  | fail error => rfl
  | div => rfl

-- Good constrains only successful audit values. The byte equation supplies
-- all error/failure/divergence correspondence, so no success-only weakening
-- is used to derive the complete audit observation equation.
theorem audit_of_bytes {S : Type} (actual : Result (Status × S))
    (modelBytes : Result ByteStatus) (good : Good actual)
    (P_proof_bytes : PV_RW_DataProduct.observe PV_RW_DataProduct.first (data actual) = modelBytes) :
    PV_RW_DataProduct.observe PV_RW_DataProduct.second (data actual) =
      PV_RW_DataProduct.observe PV_RW_DataProduct.second (attachAudit modelBytes) := by
  rw [← P_proof_bytes]
  cases actual with
  | fail error => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨status, after⟩
    cases status with
    | Err error => rfl
    | Ok pair =>
      rcases pair with ⟨proof, audit⟩
      change audit = canonical at good
      cases good
      rfl

theorem data_of_bytes {S : Type} (actual : Result (Status × S))
    (modelBytes : Result ByteStatus) (good : Good actual)
    (P_proof_bytes : PV_RW_DataProduct.observe PV_RW_DataProduct.first (data actual) = modelBytes) :
    data actual = attachAudit modelBytes := by
  apply PV_RW_DataProduct.joint
  · rw [bytes]
    exact P_proof_bytes
  · exact audit_of_bytes actual modelBytes good P_proof_bytes

#print axioms bytes
#print axioms audit_of_bytes
#print axioms data_of_bytes
end R1Z.ProverRw19AuditData
