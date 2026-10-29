import NED_RawAfterValidator
import NED_RawLiveFrontier
import NBH_ArrayEq
set_option autoImplicit false
noncomputable section
namespace NED_RawLiveValidator
open Aeneas Aeneas.Std Result WP AspisR1AdapterReconstruct
open NBD_DigestInduction NBH_Frontier
attribute [local instance] Classical.propDecidable
abbrev Snapshot := aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Error := aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1

def result (s : Snapshot) : core.result.Result Unit Error :=
  if s.pool = Array.repeat 32#usize 0#u8 ∨ s.deployment_domain = Array.repeat 32#usize 0#u8 then .Err .ZeroRequiredBinding
  else if s.sequence ≠ s.next_pair_index then .Err .SequenceIndexMismatch
  else if 1048576 ≤ s.next_pair_index.val then .Err .TreeFull
  else if Canonical s.current_root ∧ CanonicalFrom s.frontier 0 then .Ok ()
  else .Err .NonCanonicalDigest

theorem source (s : Snapshot) :
    aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 s = ok (result s) := by
  have spec : aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 s
      ⦃ r => r = result s ⦄ := by
    unfold aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1
    rw [NED_ScannerCohorts.profile_result, NED_RawLiveFrontier.live_loop]
    simp only [NBH_ArrayEq.source]
    unfold aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH
    step*
    all_goals simp_all [result]
    all_goals scalar_tac
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms source
end NED_RawLiveValidator
