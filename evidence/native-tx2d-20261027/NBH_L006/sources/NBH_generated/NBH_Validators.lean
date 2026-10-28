import NBH_LiveFrontier
set_option autoImplicit false
noncomputable section
namespace NBH_Validators
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open NBD_DigestInduction NBH_Frontier
attribute [local instance] Classical.propDecidable
abbrev Afterstate := pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev AfterError := pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1

def afterResult (a : Afterstate) : core.result.Result Unit AfterError :=
  if a.next_pair_index.val = 0 ∨ 1048576 < a.next_pair_index.val then .Err .InvalidAfterstateIndex
  else if Canonical a.next_root ∧ CanonicalFrom a.next_frontier 0 then .Ok ()
  else .Err .NonCanonicalAfterstate

theorem afterstate (a : Afterstate) :
    pool_v1.pair_terminal.validate_verified_afterstate a = ok (afterResult a) := by
  unfold pool_v1.pair_terminal.validate_verified_afterstate
  rw [NBD_DigestInduction.source, NBH_Frontier.afterstate_loop]
  have spec : (do
    if a.next_pair_index = 0#u64 then ok (.Err AfterError.InvalidAfterstateIndex)
    else
      let cap ← pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      if a.next_pair_index > cap then ok (.Err AfterError.InvalidAfterstateIndex)
      else if decide (Canonical a.next_root) then
        ok (if CanonicalFrom a.next_frontier 0 then .Ok () else .Err AfterError.NonCanonicalAfterstate)
      else ok (.Err AfterError.NonCanonicalAfterstate)) ⦃ r => r = afterResult a ⦄ := by
    unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH pool_v1.format.POOL_V1_TREE_DEPTH
    step*
    all_goals simp_all [afterResult]
    all_goals scalar_tac
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  simpa only [bind_tc_ok] using call

#print axioms afterstate
end NBH_Validators
