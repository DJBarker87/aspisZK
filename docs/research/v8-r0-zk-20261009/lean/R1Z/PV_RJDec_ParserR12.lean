import R1Z.PV_RunJoin_DecoderPrefix29
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
namespace R1Z.PV_RJDec_ParserR12
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def program (bytes : Slice U8) : P (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let i := Slice.len bytes
  if i != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES then
    pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength)
  else
    let s ← invoke "core.slice.index.Slice.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize })
    let s1 ← invoke "core.array.Array.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC { start := 0#usize, «end» := 8#usize })
    let b ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1)
    if b then
      pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongMagic)
    else
      let i1 ← invoke "Slice.index_usize" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          Slice.index_usize bytes 8#usize)
      if i1 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION then
        pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongVersion)
      else
        let i2 ← invoke "Slice.index_usize" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            Slice.index_usize bytes 9#usize)
        if i2 != 0#u8 then
          pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
        else
          let i3 ← invoke "Slice.index_usize" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              Slice.index_usize bytes 10#usize)
          if i3 != 0#u8 then
            pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
          else
            let i4 ← invoke "Slice.index_usize" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                Slice.index_usize bytes 11#usize)
            if i4 != 0#u8 then
              pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
            else
              let i5 ← invoke "Slice.index_usize" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  Slice.index_usize bytes 12#usize)
              if i5 != 0#u8 then
                pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
              else
                let i6 ← invoke "Slice.index_usize" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    Slice.index_usize bytes 13#usize)
                if i6 != 0#u8 then
                  pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                else
                  let i7 ← invoke "Slice.index_usize" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      Slice.index_usize bytes 14#usize)
                  if i7 != 0#u8 then
                    pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                  else
                    let i8 ← invoke "Slice.index_usize" (fun ops =>
                        letI : ProverRwFull.ExternalFuns := ops
                        Slice.index_usize bytes 15#usize)
                    if i8 != 0#u8 then
                      pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                    else
                      let s2 ← invoke "core.slice.index.Slice.index" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize })
                      let a ← invoke "pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING)
                      let s3 ← invoke "core.array.Array.index" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a { start := 0#usize, «end» := 32#usize })
                      let b1 ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s2 s3)
                      if b1 then
                        pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongFormatBinding)
                      else
                        let s4 ← invoke "core.slice.index.Slice.index" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 128#usize, «end» := 160#usize })
                        let r ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.array.TryFromSharedArraySlice.try_from 32#usize s4)
                        let a1 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r)
                        let r1 ← R1Z.PV_RJDec_Parser03.program a1
                        let r2 ← invoke "core.result.Result.map_err" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r1 ())
                        let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTry.branch r2)
                        match cf with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          R1Z.PV_RJDec_SnapshotChunk00.program bytes val
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)

theorem source_chunk (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) :
  erase ops (program bytes) = R1Z.PV_RunJoin_DecoderPrefix29.run bytes := by
  unfold program R1Z.PV_RunJoin_DecoderPrefix29.run
  try dsimp only
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
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro i5
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
                                · intro i6
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
                                    · intro i7
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
                                        · intro i8
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
                                            · intro s2
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro a
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro s3
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
                                                      · intro s4
                                                        try dsimp only
                                                        rw [erase_bind]
                                                        apply PV_W_RecursiveLaws.bind_congr
                                                        ·
                                                          exact erase_invoke ops _ _
                                                        · intro r
                                                          try dsimp only
                                                          rw [erase_bind]
                                                          apply PV_W_RecursiveLaws.bind_congr
                                                          ·
                                                            exact erase_invoke ops _ _
                                                          · intro a1
                                                            try dsimp only
                                                            rw [erase_bind]
                                                            apply PV_W_RecursiveLaws.bind_congr
                                                            ·
                                                              exact R1Z.PV_RJDec_Parser03.source ops a1
                                                            · intro r1
                                                              try dsimp only
                                                              rw [erase_bind]
                                                              apply PV_W_RecursiveLaws.bind_congr
                                                              ·
                                                                exact erase_invoke ops _ _
                                                              · intro r2
                                                                try dsimp only
                                                                rw [erase_bind]
                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                ·
                                                                  exact erase_invoke ops _ _
                                                                · intro cf
                                                                  try dsimp only
                                                                  cases cf with
                                                                  | Continue val =>
                                                                    exact R1Z.PV_RJDec_SnapshotChunk00.source ops bytes val
                                                                  | Break residual =>
                                                                    exact erase_invoke ops _ _

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) :
  erase ops (program bytes) = pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes :=
  (source_chunk ops bytes).trans (PV_RunJoin_DecoderPrefix29.source bytes)

#print axioms source
#print axioms source_chunk
end R1Z.PV_RJDec_ParserR12
