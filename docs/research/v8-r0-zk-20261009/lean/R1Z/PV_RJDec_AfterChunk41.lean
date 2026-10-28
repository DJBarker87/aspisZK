import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser03
import R1Z.PV_RJDec_Parser14
import R1Z.PV_RJDec_Parser05
import R1Z.PV_RJDec_SnapshotChunk20
import R1Z.PV_RJDec_SnapshotChunk16
import R1Z.PV_RJDec_SnapshotChunk12
import R1Z.PV_RJDec_SnapshotChunk08
import R1Z.PV_RJDec_SnapshotChunk04
import R1Z.PV_RJDec_SnapshotChunk00
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_AfterChunk41
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def reference (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 val35 val37 val39 val41 : Array U32 8#usize) : Result (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let s23 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 8#usize, «end» := 16#usize }
  let r63 ← pool_v1.pair_terminal.exact 8#usize s23
  let cf42 ← core.result.Result.Insts.CoreOpsTry.branch r63
  match cf42 with
  | core.ops.control_flow.ControlFlow.Continue val42 =>
    let i6 ← lift (core.num.U64.from_le_bytes val42)
    let r64 ← pool_v1.pair_terminal.validate_verified_afterstate { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) }
    let cf43 ← core.result.Result.Insts.CoreOpsTry.branch r64
    match cf43 with
    | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) })
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def program (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 val35 val37 val39 val41 : Array U32 8#usize) : P (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let s23 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 8#usize, «end» := 16#usize })
  let r63 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      pool_v1.pair_terminal.exact 8#usize s23)
  let cf42 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r63)
  match cf42 with
  | core.ops.control_flow.ControlFlow.Continue val42 =>
    let i6 ← invoke "lift" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        lift (core.num.U64.from_le_bytes val42))
    let r64 ← R1Z.PV_RJDec_Parser05.program { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) }
    let cf43 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r64)
    match cf43 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      pure (core.result.Result.Ok { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) })
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 val35 val37 val39 val41 : Array U32 8#usize) :
  erase ops (program bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 val35 val37 val39 val41) = R1Z.PV_RJDec_AfterChunk41.reference bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 val35 val37 val39 val41 := by
  unfold program R1Z.PV_RJDec_AfterChunk41.reference
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s23
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro r63
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro cf42
        try dsimp only
        cases cf42 with
        | Continue val42 =>
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro i6
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact R1Z.PV_RJDec_Parser05.source ops { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) }
            · intro r64
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro cf43
                try dsimp only
                cases cf43 with
                | Continue unused0_0 =>
                  rfl
                | Break residual =>
                  exact erase_invoke ops _ _
        | Break residual =>
          exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_AfterChunk41
