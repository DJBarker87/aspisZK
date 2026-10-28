import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser01
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Array Std.U8 216#usize) :
  P (core.result.Result pool_v1.payment_relation.CommonPublicV1 pool_v1.payment_relation.PoolV1PaymentStatementFormatError) := do
  let s ← invoke "core.array.Array.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes { start := pool_v1.payment_relation.ASSET_ID_OFFSET, «end» := pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET })
  let r ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s)
  let a ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU8) r)
  let asset ← invoke "lift" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      lift (core.num.U32.from_le_bytes a))
  if asset >= aspis_core.field.P then
    pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId)
  else
    let s1 ← invoke "core.array.Array.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes { start := pool_v1.payment_relation.POOL_OFFSET, «end» := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET })
    let r1 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s1)
    let a1 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r1)
    let s2 ← invoke "core.array.Array.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes { start := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET, «end» := pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET })
    let r2 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s2)
    let a2 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r2)
    let s3 ← invoke "core.array.Array.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes { start := pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET, «end» := pool_v1.payment_relation.ANCHOR_ROOT_OFFSET })
    let r3 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s3)
    let a3 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r3)
    let i ← invoke "lift" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        lift (core.num.U64.from_le_bytes a3))
    let s4 ← invoke "core.array.Array.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes { start := pool_v1.payment_relation.ANCHOR_ROOT_OFFSET, «end» := pool_v1.payment_relation.NULLIFIER_OFFSET })
    let r4 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.TryFromSharedArraySlice.try_from 32#usize s4)
    let a4 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r4)
    let r5 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        atomic_statement.decode_digest_canonical a4)
    let r6 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.map_err pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r5 ())
    let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r6)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s5 ← invoke "core.array.Array.index" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes { start := pool_v1.payment_relation.NULLIFIER_OFFSET, «end» := pool_v1.payment_relation.ASSET_ID_OFFSET })
      let r7 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.array.TryFromSharedArraySlice.try_from 32#usize s5)
      let a5 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r7)
      let r8 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          atomic_statement.decode_digest_canonical a5)
      let r9 ← invoke "core.result.Result.map_err" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.map_err pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r8 ())
      let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r9)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r10 ← invoke "pool_v1.payment_relation.validate_common" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            pool_v1.payment_relation.validate_common { pool := a1, deployment_domain := a2, anchor_sequence := i, anchor_root := val, nullifier := val1, asset_id := asset })
        let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r10)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          pure (core.result.Result.Ok { pool := a1, deployment_domain := a2, anchor_sequence := i, anchor_root := val, nullifier := val1, asset_id := asset })
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.payment_relation.CommonPublicV1 (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.payment_relation.CommonPublicV1 (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.payment_relation.CommonPublicV1 (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Array Std.U8 216#usize) :
  erase ops (program bytes) =
    pool_v1.payment_relation.decode_common bytes := by
  unfold program pool_v1.payment_relation.decode_common
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
        · intro asset
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
            · intro s1
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
                  · intro s2
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
                        · intro s3
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
                              · intro i
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
                                  · intro r4
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro a4
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
                                        · intro r6
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
                                              · intro s5
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro r7
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact erase_invoke ops _ _
                                                  · intro a5
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro r8
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro r9
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
                                                            · intro r10
                                                              try dsimp only
                                                              rw [erase_bind]
                                                              apply PV_W_RecursiveLaws.bind_congr
                                                              ·
                                                                exact erase_invoke ops _ _
                                                              · intro cf2
                                                                try dsimp only
                                                                cases cf2 with
                                                                | Continue unused0_0 =>
                                                                  rfl
                                                                | Break residual =>
                                                                  exact erase_invoke ops _ _
                                                          | Break residual =>
                                                            exact erase_invoke ops _ _
                                            | Break residual =>
                                              exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_Parser01
