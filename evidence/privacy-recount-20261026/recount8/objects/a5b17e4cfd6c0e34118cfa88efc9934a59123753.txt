import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser04
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ParserR18
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
  P (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError) := do
  let cpv ← invoke "pool_v1.payment_relation.transfer_common" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      pool_v1.payment_relation.transfer_common public1)
  let r ← R1Z.PV_RJDec_Parser04.program cpv
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let b ← invoke "pool_v1.payment_relation.digest_is_canonical" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        pool_v1.payment_relation.digest_is_canonical public1.recipient_commitment)
    if b then
      let b1 ← invoke "pool_v1.payment_relation.digest_is_canonical" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          pool_v1.payment_relation.digest_is_canonical public1.change_commitment)
      if b1 then
        pure (core.result.Result.Ok ())
      else
        pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)
    else
      pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
  erase ops (program public1) =
    pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 public1 := by
  unfold program pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1
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
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro b
            try dsimp only
            apply PV_W_IfLaws.erase_if_congr
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
            ·
              rfl
        | Break residual =>
          exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_ParserR18
