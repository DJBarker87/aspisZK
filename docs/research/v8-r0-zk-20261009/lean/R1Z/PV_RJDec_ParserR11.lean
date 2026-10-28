import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser04
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ParserR11
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
  P (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError) := do
  let cpv ← invoke "pool_v1.payment_relation.withdrawal_common" (fun ops =>
      letI : ExternalFuns := ops
      pool_v1.payment_relation.withdrawal_common public1)
  let r ← R1Z.PV_RJDec_Parser04.program cpv
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    if public1.amount = 0#u32 then
      pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount)
    else
      let i ← invoke "spend.VALUE_LIMIT" (fun ops =>
          letI : ExternalFuns := ops
          spend.VALUE_LIMIT)
      if public1.amount >= i then
        pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount)
      else
        let a := Array.repeat 32#usize 0#u8
        let b ← invoke "core.array.equality.PartialEqArray.eq" (fun ops =>
            letI : ExternalFuns := ops
            core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 public1.destination_token_account a)
        if b then
          pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination)
        else
          let b1 ← invoke "pool_v1.payment_relation.digest_is_canonical" (fun ops =>
              letI : ExternalFuns := ops
              pool_v1.payment_relation.digest_is_canonical public1.change_commitment)
          if b1 then
            pure (core.result.Result.Ok ())
          else
            pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
  erase ops (program public1) =
    pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 public1 := by
  unfold program pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro cpv
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact R1Z.PV_RJDec_Parser04.source ops cpv
    · intro r
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro cf
        try dsimp only
        cases cf with
        | Continue unused0_0 =>
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
                        rfl
        | Break residual =>
          exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_ParserR11
