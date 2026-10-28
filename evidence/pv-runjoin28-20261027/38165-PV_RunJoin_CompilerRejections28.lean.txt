import R1Z.PV_RunJoin_ResultDomain28
import R1Z.PV_RunJoin_UniversalRecords22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CompilerRejections28
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open R1Z.BuilderForestStdPort

/-- Exact error paths of the inner compiler, including earlier-guard
precedence. Every Try residual and error constructor is retained explicitly.
This predicate contains no call to compile_forest_from_copies. -/
def Path [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out_value : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (public1 : pair_forest_trace.ForestPublic) (lane_anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (error : pair_trace.PoolV1PairTraceErrorV1) : Prop :=
  ∃ records, (
    pool_v1.pair_forest_copy_builder.CopyRecords.new input out_value recipient
    change snapshot public1.asset
  ) = ok records ∧
  ∃ a, (
    pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.selected_commitment
    input.pair.pair_leaf input.pair.selected_second
  ) = ok a ∧
  ∃ a1, (
    pool_v1.pair_forest_copy_builder.CopyRecords.input_leaf records
  ) = ok a1 ∧
  ∃ b, (
    core.cmp.impls.PartialEqShared.ne (Array.Insts.CoreCmpPartialEqArray
    8#usize aspis_core.field.M31.Insts.CoreCmpPartialEqM31) a a1
  ) = ok b ∧
  if b
  then
    (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.SelectedCommitmentMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
  else
    ∃ a2, (
      pool_v1.pair_forest_copy_builder.CopyRecords.path_digest records 1#usize
    ) = ok a2 ∧
    ∃ r, (
      pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest
      input.pair.pair_leaf
    ) = ok r ∧
    ∃ r1, (
      core.result.Result.map_err (BuiltinFnOnce
      pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1
      pool_v1.pair_trace.PoolV1PairTraceErrorV1) r
      (pool_v1.pair_trace.PoolV1PairTraceErrorV1.PairLeafCtor)
    ) = ok r1 ∧
    ∃ cf, (
      core.result.Result.Insts.CoreOpsTry.branch r1
    ) = ok cf ∧
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      ∃ b1, (
        core.array.equality.PartialEqArray.ne
        aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a2 val
      ) = ok b1 ∧
      if b1
      then
        (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.SelectedCommitmentMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
      else
        ∃ a3, (
          pool_v1.pair_forest_copy_builder.CopyRecords.path_digest records
          21#usize
        ) = ok a3 ∧
        ∃ b2, (
          core.array.equality.PartialEqArray.ne
          aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a3 lane_anchor
        ) = ok b2 ∧
        if b2
        then
          (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.AnchorMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
        else
          ∃ nullifier, (
            pool_v1.pair_forest_copy_builder.CopyRecords.nullifier records
          ) = ok nullifier ∧
          ∃ b3, (
            core.array.equality.PartialEqArray.ne
            aspis_core.field.M31.Insts.CoreCmpPartialEqM31 nullifier
            public1.nullifier
          ) = ok b3 ∧
          if b3
          then
            (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.NullifierMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
          else
            ∃ a4, (
              pool_v1.format.pool_v1_nullifier input.pair.nullifier_key
              input.pair.salt
            ) = ok a4 ∧
            ∃ b4, (
              core.array.equality.PartialEqArray.ne
              aspis_core.field.M31.Insts.CoreCmpPartialEqM31 nullifier a4
            ) = ok b4 ∧
            if b4
            then
              (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.NullifierMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
            else
              ∃ change_commitment, (
                pool_v1.pair_forest_copy_builder.CopyRecords.change records
              ) = ok change_commitment ∧
              match public1.recipient_commitment with
              | none =>
                ∃ b5, (
                  core.array.equality.PartialEqArray.ne
                  aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                  change_commitment public1.change_commitment
                ) = ok b5 ∧
                if b5
                then
                  (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.ChangeCommitmentMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                else
                  ∃ r2, (
                    pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.single_output
                    change_commitment
                  ) = ok r2 ∧
                  ∃ r3, (
                    core.result.Result.map_err (BuiltinFnOnce
                    pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1
                    pool_v1.pair_trace.PoolV1PairTraceErrorV1) r2
                    (pool_v1.pair_trace.PoolV1PairTraceErrorV1.PairLeafCtor)
                  ) = ok r3 ∧
                  ∃ cf1, (
                    core.result.Result.Insts.CoreOpsTry.branch r3
                  ) = ok cf1 ∧
                  match cf1 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    ∃ output_pair, (
                      pool_v1.pair_forest_copy_builder.CopyRecords.output_pair
                      records
                    ) = ok output_pair ∧
                    ∃ r4, (
                      pool_v1.pair_forest_trace.late_append records snapshot
                      output_pair
                    ) = ok r4 ∧
                    ∃ cf2, (
                      core.result.Result.Insts.CoreOpsTry.branch r4
                    ) = ok cf2 ∧
                    match cf2 with
                    | core.ops.control_flow.ControlFlow.Continue val1 =>
                      ∃ s, (
                        lift (Array.to_slice input.super_root_siblings)
                      ) = ok s ∧
                      ∃ i, (
                        core.slice.Slice.iter s
                      ) = ok i ∧
                      ∃ f, (
                        core.iter.traits.iterator.Iterator.flatten.default
                        (core.iter.traits.iterator.IteratorSliceIter (Array
                        aspis_core.field.M31 8#usize))
                        (SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
                        aspis_core.field.M31 8#usize) i
                      ) = ok f ∧
                      ∃ (b6 : Bool), ∃ unused, (
                        core.iter.traits.iterator.Iterator.any.default
                        (core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator
                        (core.iter.traits.iterator.IteratorSliceIter (Array
                        aspis_core.field.M31 8#usize))
                        (SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
                        aspis_core.field.M31 8#usize)
                        (core.iter.traits.iterator.IteratorSliceIter
                        aspis_core.field.M31))
                        pool_v1.pair_forest_trace.compile_forest_from_copies.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
                        f ()
                      ) = ok (b6, unused) ∧
                      if b6
                      then
                        (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.WitnessDigest) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                      else
                        ∃ anchor, (
                          pool_v1.pair_forest_copy_builder.CopyRecords.path_digest
                          records 24#usize
                        ) = ok anchor ∧
                        ∃ b7, (
                          core.array.equality.PartialEqArray.ne
                          aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                          anchor public1.anchor
                        ) = ok b7 ∧
                        if b7
                        then
                          (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.AnchorMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                        else
                          ∃ o, (
                            pool_v1.pair_forest_copy_builder.CopyRecords.banks
                            records
                          ) = ok o ∧
                          ∃ r5, (
                            core.option.Option.ok_or o
                            pool_v1.pair_trace.PoolV1PairTraceErrorV1.Shape
                          ) = ok r5 ∧
                          ∃ cf3, (
                            core.result.Result.Insts.CoreOpsTry.branch r5
                          ) = ok cf3 ∧
                          match cf3 with
                          | core.ops.control_flow.ControlFlow.Continue val2 =>
                            ∃ r6, (
                              pool_v1.pair_forest_trace.validate_forest_poseidon_rows
                              val2
                            ) = ok r6 ∧
                            ∃ cf4, (
                              core.result.Result.Insts.CoreOpsTry.branch r6
                            ) = ok cf4 ∧
                            match cf4 with
                            | core.ops.control_flow.ControlFlow.Continue _ =>
                              ∃ private_directions, (
                                core.array.from_fn 24#usize
                                pool_v1.pair_forest_trace.compile_forest_from_copies.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
                                (input.pair, input)
                              ) = ok private_directions ∧
                              ∃ a5, (
                                pool_v1.pair_trace.value_bits input.pair.value
                              ) = ok a5 ∧
                              ∃ a6, (
                                pool_v1.pair_trace.value_bits out_value
                              ) = ok a6 ∧
                              ∃ a7, (
                                pool_v1.pair_trace.value_bits change.value
                              ) = ok a7 ∧
                              False
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
              | some expected =>
                ∃ recipient_commitment, (
                  pool_v1.pair_forest_copy_builder.CopyRecords.recipient
                  records
                ) = ok recipient_commitment ∧
                ∃ b5, (
                  core.array.equality.PartialEqArray.ne
                  aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                  recipient_commitment expected
                ) = ok b5 ∧
                if b5
                then
                  (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.RecipientCommitmentMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                else
                  ∃ b6, (
                    core.array.equality.PartialEqArray.ne
                    aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                    change_commitment public1.change_commitment
                  ) = ok b6 ∧
                  if b6
                  then
                    (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.ChangeCommitmentMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                  else
                    ∃ r2, (
                      pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.two_outputs
                      recipient_commitment change_commitment
                    ) = ok r2 ∧
                    ∃ r3, (
                      core.result.Result.map_err (BuiltinFnOnce
                      pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1
                      pool_v1.pair_trace.PoolV1PairTraceErrorV1) r2
                      (pool_v1.pair_trace.PoolV1PairTraceErrorV1.PairLeafCtor)
                    ) = ok r3 ∧
                    ∃ cf1, (
                      core.result.Result.Insts.CoreOpsTry.branch r3
                    ) = ok cf1 ∧
                    match cf1 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      ∃ output_pair, (
                        pool_v1.pair_forest_copy_builder.CopyRecords.output_pair
                        records
                      ) = ok output_pair ∧
                      ∃ r4, (
                        pool_v1.pair_forest_trace.late_append records snapshot
                        output_pair
                      ) = ok r4 ∧
                      ∃ cf2, (
                        core.result.Result.Insts.CoreOpsTry.branch r4
                      ) = ok cf2 ∧
                      match cf2 with
                      | core.ops.control_flow.ControlFlow.Continue val1 =>
                        ∃ s, (
                          lift (Array.to_slice input.super_root_siblings)
                        ) = ok s ∧
                        ∃ i, (
                          core.slice.Slice.iter s
                        ) = ok i ∧
                        ∃ f, (
                          core.iter.traits.iterator.Iterator.flatten.default
                          (core.iter.traits.iterator.IteratorSliceIter (Array
                          aspis_core.field.M31 8#usize))
                          (SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
                          aspis_core.field.M31 8#usize) i
                        ) = ok f ∧
                        ∃ (b7 : Bool), ∃ unused, (
                          core.iter.traits.iterator.Iterator.any.default
                          (core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator
                          (core.iter.traits.iterator.IteratorSliceIter (Array
                          aspis_core.field.M31 8#usize))
                          (SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
                          aspis_core.field.M31 8#usize)
                          (core.iter.traits.iterator.IteratorSliceIter
                          aspis_core.field.M31))
                          pool_v1.pair_forest_trace.compile_forest_from_copies.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
                          f ()
                        ) = ok (b7, unused) ∧
                        if b7
                        then
                          (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.WitnessDigest) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                        else
                          ∃ anchor, (
                            pool_v1.pair_forest_copy_builder.CopyRecords.path_digest
                            records 24#usize
                          ) = ok anchor ∧
                          ∃ b8, (
                            core.array.equality.PartialEqArray.ne
                            aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                            anchor public1.anchor
                          ) = ok b8 ∧
                          if b8
                          then
                            (ok (core.result.Result.Err pool_v1.pair_trace.PoolV1PairTraceErrorV1.AnchorMismatch) : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                          else
                            ∃ o, (
                              pool_v1.pair_forest_copy_builder.CopyRecords.banks
                              records
                            ) = ok o ∧
                            ∃ r5, (
                              core.option.Option.ok_or o
                              pool_v1.pair_trace.PoolV1PairTraceErrorV1.Shape
                            ) = ok r5 ∧
                            ∃ cf3, (
                              core.result.Result.Insts.CoreOpsTry.branch r5
                            ) = ok cf3 ∧
                            match cf3 with
                            | core.ops.control_flow.ControlFlow.Continue val2
                              =>
                              ∃ r6, (
                                pool_v1.pair_forest_trace.validate_forest_poseidon_rows
                                val2
                              ) = ok r6 ∧
                              ∃ cf4, (
                                core.result.Result.Insts.CoreOpsTry.branch r6
                              ) = ok cf4 ∧
                              match cf4 with
                              | core.ops.control_flow.ControlFlow.Continue _ =>
                                ∃ private_directions, (
                                  core.array.from_fn 24#usize
                                  pool_v1.pair_forest_trace.compile_forest_from_copies.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
                                  (input.pair, input)
                                ) = ok private_directions ∧
                                ∃ a5, (
                                  pool_v1.pair_trace.value_bits
                                  input.pair.value
                                ) = ok a5 ∧
                                ∃ a6, (
                                  pool_v1.pair_trace.value_bits out_value
                                ) = ok a6 ∧
                                ∃ a7, (
                                  pool_v1.pair_trace.value_bits change.value
                                ) = ok a7 ∧
                                False
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
    | core.ops.control_flow.ControlFlow.Break residual =>
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)
end R1Z.PV_RunJoin_CompilerRejections28
