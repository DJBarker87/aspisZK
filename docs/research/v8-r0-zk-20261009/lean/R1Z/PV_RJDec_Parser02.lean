import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser02
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Array Std.U8 216#usize) (magic : Array Std.U8 4#usize) (kind : pool_v1.historical_anchor.PoolV1TransitionKind) :
  P (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError) := do
  let s ← invoke "core.array.Array.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) bytes { «end» := 4#usize })
  let s1 ← invoke "core.array.Array.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) magic { start := 0#usize, «end» := 4#usize })
  let b ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1)
  if b then
    pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongMagic)
  else
    let i ← invoke "Array.index_usize" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        Array.index_usize bytes 4#usize)
    if i != pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION then
      pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongVersion)
    else
      let i1 ← invoke "Array.index_usize" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          Array.index_usize bytes 5#usize)
      let kind1 := read_discriminant kind
      let i2 ← invoke "lift" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          lift (UScalar.cast .U8 kind1))
      if i1 != i2 then
        pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongTransitionKind)
      else
        let i3 ← invoke "Array.index_usize" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            Array.index_usize bytes 6#usize)
        if i3 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION then
          pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongDigestEncoding)
        else
          let i4 ← invoke "Array.index_usize" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              Array.index_usize bytes 7#usize)
          if i4 != 0#u8 then
            pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved)
          else
            pure (core.result.Result.Ok ())

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Array Std.U8 216#usize) (magic : Array Std.U8 4#usize) (kind : pool_v1.historical_anchor.PoolV1TransitionKind) :
  erase ops (program bytes magic kind) =
    pool_v1.payment_relation.require_header bytes magic kind := by
  unfold program pool_v1.payment_relation.require_header
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro s1
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
              · intro i1
                try dsimp only
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro i2
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
                    · intro i3
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
                        · intro i4
                          try dsimp only
                          apply PV_W_IfLaws.erase_if_congr
                          ·
                            rfl
                          ·
                            rfl

#print axioms source
end R1Z.PV_RJDec_Parser02
