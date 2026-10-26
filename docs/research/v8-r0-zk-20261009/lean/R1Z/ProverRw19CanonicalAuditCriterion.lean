import R1Z.ProverRw19AuditData
import R1Z.ProverRwBodyCandidateData
set_option autoImplicit false
namespace R1Z.ProverRw19CanonicalAuditCriterion
open Aeneas Aeneas.Std Result ProverRwFull ProverRw19AuditValue
open ProverRw19AuditData ProverRwBodyDataCriterion

-- An exact criterion, rather than a supplied equation bundled into a record.
-- This still requires an independently defined mathematical byte function.
theorem data_iff {S : Type} (actual : Result (Status × S))
    (modelBytes : Result ByteStatus) (good : Good actual) :
    data actual = attachAudit modelBytes ↔
      PV_RW_DataProduct.observe PV_RW_DataProduct.first (data actual) = modelBytes := by
  constructor
  · intro same
    rw [same, bytes]
  · exact data_of_bytes actual modelBytes good

-- State writeback and byte correspondence remain separate, named statements.
-- No successful-return restriction is introduced: all four Result shapes remain.
theorem result_iff {S : Type} (actual : Result (Status × S))
    (after : S) (modelBytes : Result ByteStatus)
    (writeback : ProverRwBodyStore.Keeps after actual) (good : Good actual) :
    actual = ProverRwBodyCandidateData.withState after (attachAudit modelBytes) ↔
      PV_RW_DataProduct.observe PV_RW_DataProduct.first (data actual) = modelBytes := by
  constructor
  · intro same
    rw [same, ProverRwBodyCandidateData.data_withState, bytes]
  · intro P_proof_bytes
    exact eq_of_data after actual
      (ProverRwBodyCandidateData.withState after (attachAudit modelBytes))
      writeback (ProverRwBodyCandidateData.keeps_withState after _)
      (data_of_bytes actual modelBytes good P_proof_bytes |>.trans
        (ProverRwBodyCandidateData.data_withState after _).symm)

#print axioms data_iff
#print axioms result_iff
end R1Z.ProverRw19CanonicalAuditCriterion
