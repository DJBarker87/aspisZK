import R1Z.PV_Src_FixturePairValidation
import R1Z.PV_Src_AdmissionCommonSuccess

/-! Both release fixture inputs execute the extracted common validator. Context
and public binding remain arbitrary matching data with a fresh spent set. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_FixtureCommonValidation
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open AspisBuilderAdmissionSource
open PV_Src_AdmissionCommonSuccess PV_Src_FixturePairValidation

theorem common_success (withdrawal : Bool) (binding : Binding) (nullifier : Array U32 8#usize) :
    pool_v1.pair_trace.validate_common binding.pool binding.deployment_domain binding.anchor_sequence
      binding.anchor_root nullifier binding.asset_id (sourcePair withdrawal) (fresh binding) = ok (.Ok ()) := by
  apply success
  · exact d32_canon _
  · exact d32_canon _
  · intro l hl
    change Canon8 ((arr20 _).val[l]!)
    rw [arr20_get _ l hl]
    exact d32_canon _
  · intro h
    have hv := congrArg UScalar.val h
    change 1000 = 0 at hv
    omega
  · change 1000 < 2^30
    decide
  · change 0x54321 < 2^20
    decide
  · exact pair_spendable withdrawal

#print axioms common_success
end R1Z.PV_Src_FixtureCommonValidation
