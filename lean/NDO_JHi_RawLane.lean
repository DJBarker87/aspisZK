import NDO_JHi_RawForestDigest
import NDO_JFs_PublicLane
set_option autoImplicit false
namespace AspisR1.JHi_RawLane
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1.pair_forest_accounts

theorem source : pool_v1_pair_forest_output_lane_v1 JFt_Digest44.value=ok (.Ok 3#u8) := by
  unfold pool_v1_pair_forest_output_lane_v1
  rw [JHi_RawForestDigest.source,JFu_DigestCheck.source _ JFt_Digest44.canonical]
  simp only [bind_tc_ok,Bool.true_eq,↓reduceIte]
  unfold first_canonical_byte
  rw [JHi_DigestAssociation.encode,JFs_PublicLane.encoded]
  rfl
#print axioms source
end AspisR1.JHi_RawLane
