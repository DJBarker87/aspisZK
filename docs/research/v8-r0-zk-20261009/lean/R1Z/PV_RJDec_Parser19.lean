import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser19
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Slice Std.U8) :
  P (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) := do
  let i := Slice.len bytes
  let i1 ← invoke "pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES)
  if i != i1 then
    pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongLength)
  else
    let s ← invoke "core.slice.index.Slice.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize })
    let s1 ← invoke "core.array.Array.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC { start := 0#usize, «end» := 8#usize })
    let b ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1)
    if b then
      pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongMagic)
    else
      let i2 ← invoke "Slice.index_usize" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          Slice.index_usize bytes 8#usize)
      if i2 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION then
        pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongVersion)
      else
        let i3 ← invoke "Slice.index_usize" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            Slice.index_usize bytes 9#usize)
        if i3 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT then
          pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongItemCount)
        else
          let s2 ← invoke "core.slice.index.Slice.index" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 10#usize, «end» := 12#usize })
          let r ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.array.TryFromArrayCopySlice.try_from 2#usize core.marker.CopyU8 s2)
          let a ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 2#usize core.marker.CopyU8) r)
          let i4 ← invoke "lift" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              lift (core.num.U16.from_le_bytes a))
          let i5 ← invoke "lift" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              lift (UScalar.cast .Usize i4))
          if i5 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES then
            pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongHeaderLength)
          else
            let s3 ← invoke "core.slice.index.Slice.index" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 12#usize, «end» := 16#usize })
            let r1 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s3)
            let a1 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU8) r1)
            let i6 ← invoke "lift" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                lift (core.num.U32.from_le_bytes a1))
            let i7 ← invoke "lift" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                lift (UScalar.cast .Usize i6))
            if i7 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES then
              pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongSnapshotLength)
            else
              let s4 ← invoke "core.slice.index.Slice.index" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 20#usize })
              let r2 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s4)
              let a2 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU8) r2)
              let i8 ← invoke "lift" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  lift (core.num.U32.from_le_bytes a2))
              let i9 ← invoke "lift" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  lift (UScalar.cast .Usize i8))
              let i10 ← invoke "pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES)
              if i9 != i10 then
                pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongAfterstateLength)
              else
                let s5 ← invoke "core.slice.index.Slice.index" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 20#usize, «end» := 24#usize })
                let r3 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s5)
                let a3 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU8) r3)
                let i11 ← invoke "lift" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    lift (core.num.U32.from_le_bytes a3))
                let i12 ← invoke "lift" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    lift (UScalar.cast .Usize i11))
                if i12 != i1 then
                  pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongTotalLength)
                else
                  let i13 ← invoke "Slice.index_usize" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      Slice.index_usize bytes 24#usize)
                  if i13 != 0#u8 then
                    pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                  else
                    let i14 ← invoke "Slice.index_usize" (fun ops =>
                        letI : ProverRwFull.ExternalFuns := ops
                        Slice.index_usize bytes 25#usize)
                    if i14 != 0#u8 then
                      pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                    else
                      let i15 ← invoke "Slice.index_usize" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          Slice.index_usize bytes 26#usize)
                      if i15 != 0#u8 then
                        pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                      else
                        let i16 ← invoke "Slice.index_usize" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            Slice.index_usize bytes 27#usize)
                        if i16 != 0#u8 then
                          pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                        else
                          let i17 ← invoke "Slice.index_usize" (fun ops =>
                              letI : ProverRwFull.ExternalFuns := ops
                              Slice.index_usize bytes 28#usize)
                          if i17 != 0#u8 then
                            pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                          else
                            let i18 ← invoke "Slice.index_usize" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                Slice.index_usize bytes 29#usize)
                            if i18 != 0#u8 then
                              pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                            else
                              let i19 ← invoke "Slice.index_usize" (fun ops =>
                                  letI : ProverRwFull.ExternalFuns := ops
                                  Slice.index_usize bytes 30#usize)
                              if i19 != 0#u8 then
                                pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                              else
                                let i20 ← invoke "Slice.index_usize" (fun ops =>
                                    letI : ProverRwFull.ExternalFuns := ops
                                    Slice.index_usize bytes 31#usize)
                                if i20 != 0#u8 then
                                  pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                                else
                                  let i21 ← invoke "32#usize" (fun ops =>
                                      letI : ProverRwFull.ExternalFuns := ops
                                      32#usize + pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES)
                                  let s6 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                      letI : ProverRwFull.ExternalFuns := ops
                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 32#usize, «end» := i21 })
                                  let r4 ← invoke "pool_v1.pair_tree_profile.decode_pair_live_snapshot_boxed_v1" (fun ops =>
                                      letI : ProverRwFull.ExternalFuns := ops
                                      pool_v1.pair_tree_profile.decode_pair_live_snapshot_boxed_v1 s6)
                                  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                      letI : ProverRwFull.ExternalFuns := ops
                                      core.result.Result.Insts.CoreOpsTry.branch r4)
                                  match cf with
                                  | core.ops.control_flow.ControlFlow.Continue val =>
                                    let s7 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                        letI : ProverRwFull.ExternalFuns := ops
                                        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes { start := i21 })
                                    let r5 ← invoke "pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1" (fun ops =>
                                        letI : ProverRwFull.ExternalFuns := ops
                                        pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1 s7)
                                    let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                        letI : ProverRwFull.ExternalFuns := ops
                                        core.result.Result.Insts.CoreOpsTry.branch r5)
                                    match cf1 with
                                    | core.ops.control_flow.ControlFlow.Continue val1 =>
                                      let o ← invoke "lift" (fun ops =>
                                          letI : ProverRwFull.ExternalFuns := ops
                                          lift (U64.checked_add val.next_pair_index 1#u64))
                                      let b1 ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
                                          letI : ProverRwFull.ExternalFuns := ops
                                          core.cmp.PartialEq.ne.trait_default (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64) o (some val1.next_pair_index))
                                      if b1 then
                                        pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.AfterstateIndexMismatch)
                                      else
                                        pure (core.result.Result.Ok { live_snapshot := val, candidate_afterstate := val1 })
                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                        letI : ProverRwFull.ExternalFuns := ops
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual)
                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                      letI : ProverRwFull.ExternalFuns := ops
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Slice Std.U8) :
  erase ops (program bytes) =
    pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1 bytes := by
  unfold program pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1
  try dsimp only
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
                      · intro s2
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
                          · intro a
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro i4
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
                                  · intro s3
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro r1
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
                                          exact erase_invoke ops _ _
                                        · intro i6
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
                                              · intro s4
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
                                                  · intro a2
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro i8
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
                                                        · intro i10
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
                                                            · intro s5
                                                              try dsimp only
                                                              rw [erase_bind]
                                                              apply PV_W_RecursiveLaws.bind_congr
                                                              ·
                                                                exact erase_invoke ops _ _
                                                              · intro r3
                                                                try dsimp only
                                                                rw [erase_bind]
                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                ·
                                                                  exact erase_invoke ops _ _
                                                                · intro a3
                                                                  try dsimp only
                                                                  rw [erase_bind]
                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                  ·
                                                                    exact erase_invoke ops _ _
                                                                  · intro i11
                                                                    try dsimp only
                                                                    rw [erase_bind]
                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                    ·
                                                                      exact erase_invoke ops _ _
                                                                    · intro i12
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
                                                                        · intro i13
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
                                                                            · intro i14
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
                                                                                · intro i15
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
                                                                                    · intro i16
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
                                                                                        · intro i17
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
                                                                                            · intro i18
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
                                                                                                · intro i19
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
                                                                                                    · intro i20
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
                                                                                                        · intro i21
                                                                                                          try dsimp only
                                                                                                          rw [erase_bind]
                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                          ·
                                                                                                            exact erase_invoke ops _ _
                                                                                                          · intro s6
                                                                                                            try dsimp only
                                                                                                            rw [erase_bind]
                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                            ·
                                                                                                              exact erase_invoke ops _ _
                                                                                                            · intro r4
                                                                                                              try dsimp only
                                                                                                              rw [erase_bind]
                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                              ·
                                                                                                                exact erase_invoke ops _ _
                                                                                                              · intro cf
                                                                                                                try dsimp only
                                                                                                                cases cf with
                                                                                                                | Continue val =>
                                                                                                                  try dsimp only
                                                                                                                  rw [erase_bind]
                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                  ·
                                                                                                                    exact erase_invoke ops _ _
                                                                                                                  · intro s7
                                                                                                                    try dsimp only
                                                                                                                    rw [erase_bind]
                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                    ·
                                                                                                                      exact erase_invoke ops _ _
                                                                                                                    · intro r5
                                                                                                                      try dsimp only
                                                                                                                      rw [erase_bind]
                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                      ·
                                                                                                                        exact erase_invoke ops _ _
                                                                                                                      · intro cf1
                                                                                                                        try dsimp only
                                                                                                                        cases cf1 with
                                                                                                                        | Continue val1 =>
                                                                                                                          try dsimp only
                                                                                                                          rw [erase_bind]
                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                          ·
                                                                                                                            exact erase_invoke ops _ _
                                                                                                                          · intro o
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
                                                                                                                | Break residual =>
                                                                                                                  exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_Parser19
