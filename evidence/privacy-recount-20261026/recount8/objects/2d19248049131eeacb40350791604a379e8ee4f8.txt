import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser04
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (common : pool_v1.payment_relation.CommonPublicV1) :
  P (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError) := do
  let a := Array.repeat 32#usize 0#u8
  let b ← invoke "core.array.equality.PartialEqArray.eq" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.pool a)
  if b then
    pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding)
  else
    let a1 := Array.repeat 32#usize 0#u8
    let b1 ← invoke "core.array.equality.PartialEqArray.eq" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.deployment_domain a1)
    if b1 then
      pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding)
    else
      let i ← invoke "pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY)
      if common.anchor_sequence > i then
        pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence)
      else
        let b2 ← invoke "pool_v1.payment_relation.digest_is_canonical" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            pool_v1.payment_relation.digest_is_canonical common.anchor_root)
        if b2 then
          let b3 ← invoke "pool_v1.payment_relation.digest_is_canonical" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              pool_v1.payment_relation.digest_is_canonical common.nullifier)
          if b3 then
            let i1 := common.asset_id
            if i1 >= aspis_core.field.P then
              pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId)
            else
              pure (core.result.Result.Ok ())
          else
            pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)
        else
          pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)

theorem source (ops : ProverRwFull.ExternalFuns)
  (common : pool_v1.payment_relation.CommonPublicV1) :
  erase ops (program common) =
    pool_v1.payment_relation.validate_common common := by
  unfold program pool_v1.payment_relation.validate_common
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
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro b3
                    try dsimp only
                    apply PV_W_IfLaws.erase_if_congr
                    ·
                      try dsimp only
                      try dsimp only
                      apply PV_W_IfLaws.erase_if_congr
                      ·
                        rfl
                      ·
                        rfl
                    ·
                      rfl
                ·
                  rfl

#print axioms source
end R1Z.PV_RJDec_Parser04
