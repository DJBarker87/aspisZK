import NFY_Part053
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_ChildLaws
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Consume the existing CLOSED scanner packet at the exact digest. -/
theorem scanner (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical d =
      ok (decide (NBD_DigestInduction.Canonical d)) :=
  NFY_NED_ScannerCohorts.account_result d

/-- Consume the existing CLOSED first-byte packet at the exact digest. -/
theorem first (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.first_canonical_byte d =
      ok (NFY_NBN_OutputLane.first d) := by
  rw [NFY_NED_DigestCohorts.first_byte]
  exact NFY_NBN_OutputLane.first_source d

#print axioms scanner
#print axioms first
end PCF_ChildLaws
