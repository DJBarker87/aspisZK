import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser14
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
  P (core.result.Result Unit pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) := do
  let a := Array.repeat 32#usize 0#u8
  let b ← invoke "core.array.equality.PartialEqArray.eq" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 snapshot.pool a)
  if b then
    pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.ZeroRequiredBinding)
  else
    let a1 := Array.repeat 32#usize 0#u8
    let b1 ← invoke "core.array.equality.PartialEqArray.eq" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 snapshot.deployment_domain a1)
    if b1 then
      pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.ZeroRequiredBinding)
    else
      if snapshot.sequence != snapshot.next_pair_index then
        pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.SequenceIndexMismatch)
      else
        let i ← invoke "pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY)
        if snapshot.next_pair_index >= i then
          pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.TreeFull)
        else
          let b2 ← invoke "pool_v1.pair_tree_profile.digest_is_canonical" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              pool_v1.pair_tree_profile.digest_is_canonical snapshot.current_root)
          if b2 then
            invoke "pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop snapshot.frontier 0#usize)
          else
            pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonCanonicalDigest)

theorem source (ops : ProverRwFull.ExternalFuns)
  (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
  erase ops (program snapshot) =
    pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 snapshot := by
  unfold program pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1
  try dsimp only
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro b
    try dsimp only
    apply PV_W_IfLaws.erase_if_congr
    ·
      rfl
    ·
      try dsimp only
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro b1
        try dsimp only
        apply PV_W_IfLaws.erase_if_congr
        ·
          rfl
        ·
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
                · intro b2
                  try dsimp only
                  apply PV_W_IfLaws.erase_if_congr
                  ·
                    exact erase_invoke ops _ _
                  ·
                    rfl

#print axioms source
end R1Z.PV_RJDec_Parser14
