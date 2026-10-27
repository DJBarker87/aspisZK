import R1Z.PV_RW_DataProduct
import R1Z.ProverRwBodyCandidateData
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_DataPartsIff
open Aeneas Aeneas.Std Result ProverRwBodyDataCriterion ProverRwBodyStore

theorem exact_criterion {Proof Audit Verifier State : Type} (after : State)
    (actual : Result ((core.result.Result (Proof × Audit) Verifier) × State))
    (model : Result (core.result.Result (Proof × Audit) Verifier))
    (kept : Keeps after actual) :
    actual=ProverRwBodyCandidateData.withState after model ↔
      (PV_RW_DataProduct.observe PV_RW_DataProduct.first (data actual)=
        PV_RW_DataProduct.observe PV_RW_DataProduct.first model ∧
       PV_RW_DataProduct.observe PV_RW_DataProduct.second (data actual)=
        PV_RW_DataProduct.observe PV_RW_DataProduct.second model) := by
  constructor
  · intro same
    have hd : data actual=model := by
      rw [same,ProverRwBodyCandidateData.data_withState]
    exact (PV_RW_DataProduct.equal_iff _ model).mp hd
  · rintro ⟨proofData,auditData⟩
    apply eq_of_data after _ _ kept (ProverRwBodyCandidateData.keeps_withState after model)
    rw [ProverRwBodyCandidateData.data_withState]
    exact PV_RW_DataProduct.joint _ model proofData auditData
#print axioms exact_criterion
end R1Z.PV_RW_DataPartsIff
