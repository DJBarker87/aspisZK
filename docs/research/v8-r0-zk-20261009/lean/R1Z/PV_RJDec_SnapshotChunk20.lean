import R1Z.PV_RunJoin_DecoderStage2029
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser03
import R1Z.PV_RJDec_Parser14
import R1Z.PV_RJDec_Parser05
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_SnapshotChunk20
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def program (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize) : P (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s25 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize })
  let r63 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s25)
  let a22 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r63)
  let s26 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize })
  let r64 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s26)
  let a23 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r64)
  let s27 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 120#usize })
  let r65 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s27)
  let a24 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r65)
  let i9 ← invoke "lift" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      lift (core.num.U64.from_le_bytes a24))
  let s28 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 120#usize, «end» := 128#usize })
  let r66 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s28)
  let a25 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r66)
  let i10 ← invoke "lift" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      lift (core.num.U64.from_le_bytes a25))
  let r67 ← R1Z.PV_RJDec_Parser14.program { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }
  let cf21 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r67)
  match cf21 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    pure (core.result.Result.Ok { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) })
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize) :
  erase ops (program bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20) = R1Z.PV_RunJoin_DecoderStage2029.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 := by
  unfold program R1Z.PV_RunJoin_DecoderStage2029.run
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s25
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
      · intro a22
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro s26
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro r64
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro a23
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro s27
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro r65
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro a24
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro i9
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro s28
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro r66
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke ops _ _
                          · intro a25
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro i10
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact R1Z.PV_RJDec_Parser14.source ops { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }
                              · intro r67
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro cf21
                                  try dsimp only
                                  cases cf21 with
                                  | Continue unused0_0 =>
                                    rfl
                                  | Break residual =>
                                    exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_SnapshotChunk20
