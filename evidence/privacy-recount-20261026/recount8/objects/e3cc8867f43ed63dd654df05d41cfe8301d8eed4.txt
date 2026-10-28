import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser00
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (byte : Std.U8) :
  P (core.result.Result pool_v1.historical_anchor.PoolV1TransitionKind pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let i ← invoke "1#u8" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      1#u8 + 0#u8)
  let i1 ← invoke "lift" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      lift (UScalar.cast .U8 i))
  if byte = i1 then
    pure (core.result.Result.Ok pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer)
  else
    let i2 ← invoke "2#u8" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        2#u8 + 0#u8)
    let i3 ← invoke "lift" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        lift (UScalar.cast .U8 i2))
    if byte = i3 then
      pure (core.result.Result.Ok pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal)
    else
      pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.InvalidTransitionKind)

theorem source (ops : ProverRwFull.ExternalFuns)
  (byte : Std.U8) :
  erase ops (program byte) =
    pool_v1.pair_forest_terminal.transition_kind byte := by
  unfold program pool_v1.pair_forest_terminal.transition_kind
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro i
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro i1
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
        · intro i2
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro i3
            try dsimp only
            apply PV_W_IfLaws.erase_if_congr
            ·
              rfl
            ·
              rfl

#print axioms source
end R1Z.PV_RJDec_Parser00
