import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser05
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (afterstate : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
  P (core.result.Result Unit pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  if afterstate.next_pair_index = 0#u64 then
    pure (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidAfterstateIndex)
  else
    let i ← invoke "pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY)
    if afterstate.next_pair_index > i then
      pure (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidAfterstateIndex)
    else
      let b ← invoke "pool_v1.pair_tree_profile.digest_is_canonical" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          pool_v1.pair_tree_profile.digest_is_canonical afterstate.next_root)
      if b then
        invoke "pool_v1.pair_terminal.validate_verified_afterstate_loop" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          pool_v1.pair_terminal.validate_verified_afterstate_loop afterstate.next_frontier 0#usize)
      else
        pure (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.NonCanonicalAfterstate)

theorem source (ops : ProverRwFull.ExternalFuns)
  (afterstate : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
  erase ops (program afterstate) =
    pool_v1.pair_terminal.validate_verified_afterstate afterstate := by
  unfold program pool_v1.pair_terminal.validate_verified_afterstate
  try dsimp only
  apply PV_W_IfLaws.erase_if_congr
  ·
    rfl
  ·
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro i
      try dsimp only
      apply PV_W_IfLaws.erase_if_congr
      ·
        rfl
      ·
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro b
          try dsimp only
          apply PV_W_IfLaws.erase_if_congr
          ·
            exact erase_invoke ops _ _
          ·
            rfl

#print axioms source
end R1Z.PV_RJDec_Parser05
