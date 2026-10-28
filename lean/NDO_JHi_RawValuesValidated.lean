import NDO_JHi_RawSnapshotValidator
import NDO_JHi_RawAfterstateValidator
import NDO_JHg_RawPrefix
import NDO_JFu_DigestSliceCanonical
set_option autoImplicit false
namespace AspisR1.JHi_RawValuesValidated
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

theorem snapshot : aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1
    JHg_RawCommon.common.lane_transition.live_snapshot=ok (.Ok ()) := by
  apply JHi_RawSnapshotValidator.source
  · exact JFu_PublicBindings.pool_nonzero
  · exact JFu_PublicBindings.domain_nonzero
  · rfl
  · decide
  · exact JFt_Digest01.canonical
  · intro i
    exact JFu_DigestSliceCanonical.source _ _ (JFt_SnapshotValue.frontier i)
#print axioms snapshot

theorem afterstate : aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate
    JHg_RawCommon.common.lane_transition.candidate_afterstate=ok (.Ok ()) := by
  apply JHi_RawAfterstateValidator.source
  · decide
  · decide
  · exact JFt_Digest22.canonical
  · exact JFt_AfterstateValue.frontier
#print axioms afterstate
end AspisR1.JHi_RawValuesValidated
