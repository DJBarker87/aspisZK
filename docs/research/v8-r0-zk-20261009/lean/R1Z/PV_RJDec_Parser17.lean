import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser17
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Slice Std.U8) :
  P (core.result.Result pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 pool_v1.payment_relation.PoolV1PaymentStatementFormatError) := do
  let r ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.TryFromSharedArraySlice.try_from 216#usize bytes)
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.map_err pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError r ())
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r2 ← invoke "pool_v1.payment_relation.require_header" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        pool_v1.payment_relation.require_header val pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer)
    let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r2)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s ← invoke "core.array.Array.index" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) val { start := pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET, «end» := pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET })
      let a ← invoke "lift" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          lift (core.num.U32.to_le_bytes pool_v1.payment_relation.POOL_V1_CANONICAL_FEE))
      let s1 ← invoke "core.array.Array.index" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a { start := 0#usize, «end» := 4#usize })
      let b ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1)
      if b then
        pure (core.result.Result.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved)
      else
        let r3 ← invoke "pool_v1.payment_relation.decode_common" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            pool_v1.payment_relation.decode_common val)
        let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r3)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let s2 ← invoke "core.array.Array.index" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) val { start := pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET, «end» := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET })
          let r4 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.array.TryFromSharedArraySlice.try_from 32#usize s2)
          let a1 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r4)
          let r5 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              atomic_statement.decode_digest_canonical a1)
          let r6 ← invoke "core.result.Result.map_err" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.map_err pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r5 ())
          let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTry.branch r6)
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s3 ← invoke "core.array.Array.index" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) val { start := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET })
            let r7 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.array.TryFromSharedArraySlice.try_from 32#usize s3)
            let a2 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r7)
            let r8 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                atomic_statement.decode_digest_canonical a2)
            let r9 ← invoke "core.result.Result.map_err" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.map_err pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r8 ())
            let cf4 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTry.branch r9)
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r10 ← invoke "pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 { pool := val1.pool, deployment_domain := val1.deployment_domain, anchor_sequence := val1.anchor_sequence, anchor_root := val1.anchor_root, nullifier := val1.nullifier, asset_id := val1.asset_id, recipient_commitment := val2, change_commitment := val3 })
              let cf5 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTry.branch r10)
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                pure (core.result.Result.Ok { pool := val1.pool, deployment_domain := val1.deployment_domain, anchor_sequence := val1.anchor_sequence, anchor_root := val1.anchor_root, nullifier := val1.nullifier, asset_id := val1.asset_id, recipient_commitment := val2, change_commitment := val3 })
              | core.ops.control_flow.ControlFlow.Break residual =>
                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)
            | core.ops.control_flow.ControlFlow.Break residual =>
              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)
          | core.ops.control_flow.ControlFlow.Break residual =>
            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Slice Std.U8) :
  erase ops (program bytes) =
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 bytes := by
  unfold program pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1
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
    · intro r1
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
          · intro r2
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro cf1
              try dsimp only
              cases cf1 with
              | Continue unused0_0 =>
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
                  · intro a
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
                          · intro r3
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro cf2
                              try dsimp only
                              cases cf2 with
                              | Continue val1 =>
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
                                  · intro r4
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
                                          · intro cf3
                                            try dsimp only
                                            cases cf3 with
                                            | Continue val2 =>
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
                                                · intro r7
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
                                                        · intro cf4
                                                          try dsimp only
                                                          cases cf4 with
                                                          | Continue val3 =>
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
                                                              · intro cf5
                                                                try dsimp only
                                                                cases cf5 with
                                                                | Continue unused0_0 =>
                                                                  rfl
                                                                | Break residual =>
                                                                  exact erase_invoke ops _ _
                                                          | Break residual =>
                                                            exact erase_invoke ops _ _
                                            | Break residual =>
                                              exact erase_invoke ops _ _
                              | Break residual =>
                                exact erase_invoke ops _ _
              | Break residual =>
                exact erase_invoke ops _ _
        | Break residual =>
          exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_Parser17
