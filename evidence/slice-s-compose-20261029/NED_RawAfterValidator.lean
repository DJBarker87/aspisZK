import NED_RawAfterFrontier
set_option autoImplicit false
noncomputable section
namespace NED_RawAfterValidator
open Aeneas Aeneas.Std Result WP AspisR1AdapterReconstruct
open NBD_DigestInduction NBH_Frontier
attribute [local instance] Classical.propDecidable
abbrev Afterstate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev AfterError := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1

def afterResult (a : Afterstate) : core.result.Result Unit AfterError :=
  if a.next_pair_index.val = 0 ∨ 1048576 < a.next_pair_index.val then .Err .InvalidAfterstateIndex
  else if Canonical a.next_root ∧ CanonicalFrom a.next_frontier 0 then .Ok ()
  else .Err .NonCanonicalAfterstate

theorem afterstate (a : Afterstate) :
    aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate a = ok (afterResult a) := by
  have spec : aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate a
      ⦃ r => r = afterResult a ⦄ := by
    unfold aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate
    rw [NED_ScannerCohorts.profile_result, NED_RawAfterFrontier.afterstate_loop]
    unfold aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH
    step*
    all_goals simp_all [afterResult]
    all_goals scalar_tac
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms afterstate
end NED_RawAfterValidator
