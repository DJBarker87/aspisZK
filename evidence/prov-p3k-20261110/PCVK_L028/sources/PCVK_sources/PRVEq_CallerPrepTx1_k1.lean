-- PCVK_ CurrentCompactCaller prepare/tx1: fresh = gate. Fresh text: PCVJ_E002 emission (Aeneas b59d5188-extended, overflow ON, frozen 4bb3b3f), externals as fields of Ext.
-- RESULT CLASS: CONDITIONAL_ON_BINDING (see Bound). Statement: for every ops and x with Bound ops x, fresh x = gate ops.
import Aeneas
import CurrentCompactCallerModelV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1CurrentCaller
namespace PCVK_C

structure Ext where
  aspis_core_field_wide_exact_WideExact_ZERO : Result aspis_core.field.wide_exact.WideExact
  verifier_candidate_canonical_scan : (Slice Std.U8) → Result (core.result.Result Unit verifier.Error)
  verifier_QueryGeometry_for_range : (Array Std.U32 22#usize) → Std.Usize → Std.Usize → Result (core.result.Result verifier.QueryGeometry verifier.Error)
  verifier_candidate_batch_merkle : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), (Slice Std.U8) → verifier.Prepared → (Array Std.U8 32#usize) → Std.Usize → H → Result (core.result.Result Unit verifier.Error)
  verifier_candidate_parse_shape : (Slice Std.U8) → Result (core.result.Result transport.Variant verifier.Error)
  verifier_BatchedWeights_finish : verifier.BatchedWeights → (Slice aspis_core.field.QM31) → Result (Slice aspis_core.field.QM31)
  verifier_candidate_query_loop : (Slice Std.U8) → verifier.Prepared → verifier.Accumulator → (Array aspis_core.field.wide_exact.WideExact 29#usize) → (Option (verifier.Phase → Result Unit)) → verifier.QueryGeometry → verifier.BatchedWeights → Std.Usize → Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
  verifier_candidate_wide_view : (Slice Std.U8) → (Slice Std.U8) → (Slice Std.U8) → Result (core.result.Result verifier.View verifier.Error)
  r1_semantic_verify_observed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice Std.U8) → H → (Option (verifier.Phase → Result Unit)) → Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  verifier_BatchedWeights_new : (Slice aspis_core.field.QM31) → Result (core.result.Result verifier.BatchedWeights verifier.Error)
  aspis_core_r0_heap_filled : ∀ {T : Type} (coremarkerCopyInst : core.marker.Copy T), Std.Usize → T → Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error)
  verifier_Accumulator_new : transport.Variant → Result (core.result.Result verifier.Accumulator verifier.Error)
  compact_expand_semantic : (Slice Std.U8) → (Slice Std.U8) → Result ((core.result.Result Unit compact.CodecError) × (Slice Std.U8))
  verifier_Prepared_new : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), (r1_semantic.Verified H) → verifier.View → H → (Array aspis_core.field.wide_exact.WideExact 29#usize) → Result ((core.result.Result verifier.Prepared verifier.Error) × (Array aspis_core.field.wide_exact.WideExact 29#usize))
  compact_expand_values : (Slice Std.U8) → (Slice Std.U8) → Result ((core.result.Result Unit compact.CodecError) × (Slice Std.U8))
  verifier_checkpoint : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), verifier.Prepared → verifier.Accumulator → (Slice Std.U8) → (Slice Std.U8) → H → Result (alloc.vec.Vec Std.U8)
  verifier_mark : (Option (verifier.Phase → Result Unit)) → verifier.Phase → Result Unit

def verifier.Error.Insts.CoreConvertFromCodecError.from
  (ce : compact.CodecError) : Result verifier.Error := do
  ok verifier.Error.Parse

@[reducible]
def verifier.Error.Insts.CoreConvertFromCodecError : core.convert.From
  verifier.Error compact.CodecError := {
  «from» := verifier.Error.Insts.CoreConvertFromCodecError.from
}

@[global_simps, irreducible] def compact.HEADER : Std.Usize := 16#usize

@[global_simps, irreducible]
def compact.OFF_SEMANTIC : Std.Usize := compact.HEADER

@[global_simps, irreducible]
def compact.SEMANTIC_COMPACT_VALUES : Result Std.Usize := do
  let i ← 10#usize * 28#usize
  let i1 ← 1#usize + i
  let i2 ← 87#usize + 29#usize
  let i3 ← i1 + i2
  i3 + 29#usize

@[global_simps, irreducible]
def verifier.SEMANTIC_BYTES : Result Std.Usize := do
  let i ← 29#usize * 32#usize
  12903#usize + i

@[global_simps, irreducible]
def compact.LOGICAL_SEMANTIC : Result Std.Usize := verifier.SEMANTIC_BYTES

@[global_simps, irreducible]
def compact.COMPACT_SEMANTIC : Result Std.Usize := do
  let i ← compact.SEMANTIC_COMPACT_VALUES
  let i1 ← 16#usize * i
  let i2 ← compact.LOGICAL_SEMANTIC
  i2 - i1

@[global_simps, irreducible]
def compact.OFF_Y1 : Result Std.Usize := do
  let i ← compact.COMPACT_SEMANTIC
  compact.OFF_SEMANTIC + i

@[global_simps, irreducible]
def compact.COMPACT_Y1 : Result Std.Usize := 29#usize * 16#usize

@[global_simps, irreducible]
def compact.OFF_INACTIVE : Result Std.Usize := do
  let i ← compact.OFF_Y1
  let i1 ← compact.COMPACT_Y1
  i + i1

@[global_simps, irreducible]
def compact.LOGICAL_Y1 : Result Std.Usize := 29#usize * 32#usize

def
  verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (c : verifier.candidate.prepare.closure_1 H) (tupled_args : r1_wire.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Semantic

@[reducible]
def
  verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
  core.ops.function.FnOnce (verifier.candidate.prepare.closure_1 H)
  r1_wire.Error verifier.Error := {
  call_once :=
    verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
    aspis_coredigestDigest32Inst
}

def
  verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (c : verifier.candidate.prepare.closure H)
  (tupled_args : aspis_core.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Allocation

@[reducible]
def
  verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
  core.ops.function.FnOnce (verifier.candidate.prepare.closure H)
  aspis_core.r0.Error verifier.Error := {
  call_once :=
    verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
    aspis_coredigestDigest32Inst
}

def verifier.candidate.prepare (x : Ext)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (proof : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit))
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  Result ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 29#usize))
  := do
  let i ← compact.LOGICAL_SEMANTIC
  let i1 ← compact.LOGICAL_Y1
  let i2 ← i + i1
  let r ← x.aspis_core_r0_heap_filled core.marker.CopyU8 i2 0#u8
  let r1 ←
    core.result.Result.map_err
      (verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      aspis_coredigestDigest32Inst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut val)
    let ((semantic, y1), split_at_mut_back) ←
      core.slice.Slice.split_at_mut s i
    let i3 ← compact.OFF_Y1
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) proof { start := compact.OFF_SEMANTIC, «end» := i3 }
    let (r2, semantic1) ← x.compact_expand_semantic s1 semantic
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let i4 ← compact.OFF_INACTIVE
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i3, «end» := i4 }
      let (r3, y11) ← x.compact_expand_values s2 y1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s3 := split_at_mut_back (semantic1, y11)
        let val1 := deref_mut_back s3
        let s4 ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice
            Std.U8) val1 { «end» := i }
        let s5 ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice
            Std.U8) val1 { start := i }
        let r4 ← x.verifier_candidate_wide_view proof s4 s5
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue v =>
          let r5 ←
            x.r1_semantic_verify_observed aspis_coredigestDigest32Inst public1
              v.semantic hash obs
          let r6 ←
            core.result.Result.map_err
              (verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
              aspis_coredigestDigest32Inst) r5 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r6
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            x.verifier_mark obs verifier.Phase.Semantic
            x.verifier_Prepared_new aspis_coredigestDigest32Inst val2 v hash g
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r7 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                verifier.Prepared (core.convert.FromSame verifier.Error)
                residual
            ok (r7, g)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r5 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              verifier.Prepared (core.convert.FromSame verifier.Error) residual
          ok (r5, g)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.Prepared verifier.Error.Insts.CoreConvertFromCodecError
            residual
        ok (r4, g)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared verifier.Error.Insts.CoreConvertFromCodecError
          residual
      ok (r3, g)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.Prepared (core.convert.FromSame verifier.Error) residual
    ok (r2, g)

@[global_simps, irreducible]
def compact.OFF_ROUND0 : Result Std.Usize := do
  let i ← compact.OFF_INACTIVE
  i + 32#usize

@[global_simps, irreducible]
def compact.OFF_FOLDED_ROOT : Result Std.Usize := do
  let i ← compact.OFF_ROUND0
  i + 224#usize

@[global_simps, irreducible]
def compact.OFF_ROUND1 : Result Std.Usize := do
  let i ← compact.OFF_FOLDED_ROOT
  i + 32#usize

@[global_simps, irreducible] def compact.SPLIT : Std.Usize := 10#usize

def verifier.candidate.tx1 (x : Ext)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
  (hash : H) (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  if k != compact.SPLIT
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    let r ← x.verifier_candidate_parse_shape proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← x.verifier_candidate_canonical_scan proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        x.verifier_mark obs verifier.Phase.Parsed
        let we ← x.aspis_core_field_wide_exact_WideExact_ZERO
        let g := Array.repeat 29#usize we
        let (r2, g1) ←
          (verifier.candidate.prepare x) aspis_coredigestDigest32Inst public1 proof
            hash obs g
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let r3 ← x.verifier_Accumulator_new transport.Variant.S2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            x.verifier_mark obs verifier.Phase.Prepare
            let i ← compact.OFF_FOLDED_ROOT
            let i1 ← compact.OFF_ROUND1
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                { start := i, «end» := i1 }
            let r4 ←
              core.array.TryFromArrayCopySlice.try_from 32#usize
                core.marker.CopyU8 s
            let folded_root ←
              core.result.Result.unwrap core.fmt.DebugTryFromSliceError r4
            let r5 ←
              x.verifier_candidate_batch_merkle aspis_coredigestDigest32Inst
                proof val folded_root 0#usize hash
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              x.verifier_mark obs (verifier.Phase.Merkle 0#usize)
              let r6 ← x.verifier_QueryGeometry_for_range val.queries 0#usize k
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                let s1 := alloc.vec.Vec.deref val1.weights
                let r7 ← x.verifier_BatchedWeights_new s1
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let r8 ←
                    x.verifier_candidate_query_loop proof val val1 g1 obs val2
                      val3 k
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let (a, pending) := val4
                    let (s2, deref_mut_back) ←
                      lift (alloc.vec.Vec.deref_mut a.weights)
                    let s3 ← x.verifier_BatchedWeights_finish pending s2
                    let v := deref_mut_back s3
                    let bytes ←
                      x.verifier_checkpoint aspis_coredigestDigest32Inst val
                        { a with weights := v } proof public_bytes hash
                    x.verifier_mark obs verifier.Phase.CheckpointWrite
                    ok (core.result.Result.Ok bytes)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      verifier.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    verifier.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

structure Bound (ops : Ops) (x : Ext) : Prop where
  h_aspis_core_field_wide_exact_WideExact_ZERO : x.aspis_core_field_wide_exact_WideExact_ZERO = AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO ops
  h_verifier_candidate_canonical_scan : x.verifier_candidate_canonical_scan = ops.op4
  h_verifier_QueryGeometry_for_range : x.verifier_QueryGeometry_for_range = ops.op19
  h_verifier_candidate_batch_merkle : @x.verifier_candidate_batch_merkle = @ops.op6
  h_verifier_candidate_parse_shape : x.verifier_candidate_parse_shape = ops.op3
  h_verifier_BatchedWeights_finish : x.verifier_BatchedWeights_finish = ops.op17
  h_verifier_candidate_query_loop : x.verifier_candidate_query_loop = ops.op7
  h_verifier_candidate_wide_view : x.verifier_candidate_wide_view = ops.op5
  h_r1_semantic_verify_observed : @x.r1_semantic_verify_observed = @ops.op9
  h_verifier_BatchedWeights_new : x.verifier_BatchedWeights_new = ops.op18
  h_aspis_core_r0_heap_filled : @x.aspis_core_r0_heap_filled = @ops.op1
  h_verifier_Accumulator_new : x.verifier_Accumulator_new = ops.op20
  h_compact_expand_semantic : x.compact_expand_semantic = ops.op10
  h_verifier_Prepared_new : @x.verifier_Prepared_new = @ops.op8
  h_compact_expand_values : x.compact_expand_values = ops.op11
  h_verifier_checkpoint : @x.verifier_checkpoint = @ops.op16
  h_verifier_mark : x.verifier_mark = AspisR1CurrentCaller.verifier.mark
  h_op2 : ops.op2 = AspisR1CurrentCaller.PCVK_C.verifier.Error.Insts.CoreConvertFromCodecError.from
  h_op12 : ops.op12 = ok AspisR1CurrentCaller.PCVK_C.compact.OFF_SEMANTIC
  h_op13 : ops.op13 = AspisR1CurrentCaller.PCVK_C.compact.COMPACT_SEMANTIC
  h_op14 : ops.op14 = AspisR1CurrentCaller.PCVK_C.compact.COMPACT_Y1
  h_op15 : ops.op15 = AspisR1CurrentCaller.PCVK_C.compact.LOGICAL_SEMANTIC
  h_op21 : ops.op21 = AspisR1CurrentCaller.PCVK_C.compact.OFF_ROUND0

end PCVK_C
end AspisR1CurrentCaller

theorem PRVEq_C_cp0 : AspisR1CurrentCaller.PCVK_C.compact.LOGICAL_Y1 = AspisR1CurrentCaller.compact.LOGICAL_Y1 := by
  unfold AspisR1CurrentCaller.PCVK_C.compact.LOGICAL_Y1 AspisR1CurrentCaller.compact.LOGICAL_Y1
  rfl

theorem PRVEq_C_cp1 : AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = AspisR1CurrentCaller.verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once := by
  unfold AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once AspisR1CurrentCaller.verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  rfl

theorem PRVEq_C_cp2 : AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError = AspisR1CurrentCaller.verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError := by
  unfold AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError AspisR1CurrentCaller.verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
  rfl

theorem PRVEq_C_cp3 : AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = AspisR1CurrentCaller.verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once := by
  unfold AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once AspisR1CurrentCaller.verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  rfl

theorem PRVEq_C_cp4 : AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError = AspisR1CurrentCaller.verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError := by
  unfold AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError AspisR1CurrentCaller.verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
  rfl


open Lean Meta Elab Tactic in
/-- unfold every matcher constant occurring in the goal (fresh and gate matchers are separate constants with equal bodies). -/
elab "delta_matchers" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let env ← getEnv
  let names := ty.foldConsts (#[] : Array Name) fun c a => if Lean.Meta.isMatcherCore env c then a.push c else a
  if names.isEmpty then return
  let ids := names.map (fun n => mkIdent n)
  evalTactic (← `(tactic| delta $ids:ident*))

namespace PRVEq.CallerPrepTx1_k1
variable {ops : AspisR1CurrentCaller.Ops} {x : AspisR1CurrentCaller.PCVK_C.Ext} (b : AspisR1CurrentCaller.PCVK_C.Bound ops x)
include b

theorem c_off_semantic : AspisR1CurrentCaller.compact.OFF_SEMANTIC ops = ok AspisR1CurrentCaller.PCVK_C.compact.OFF_SEMANTIC := by
  unfold AspisR1CurrentCaller.compact.OFF_SEMANTIC
  exact b.h_op12

theorem c_off_y1 : AspisR1CurrentCaller.compact.OFF_Y1 ops = AspisR1CurrentCaller.PCVK_C.compact.OFF_Y1 := by
  unfold AspisR1CurrentCaller.compact.OFF_Y1 AspisR1CurrentCaller.PCVK_C.compact.OFF_Y1
  simp only [c_off_semantic b, b.h_op13, bind_tc_ok]

theorem c_off_inactive : AspisR1CurrentCaller.compact.OFF_INACTIVE ops = AspisR1CurrentCaller.PCVK_C.compact.OFF_INACTIVE := by
  unfold AspisR1CurrentCaller.compact.OFF_INACTIVE AspisR1CurrentCaller.PCVK_C.compact.OFF_INACTIVE
  simp only [c_off_y1 b, b.h_op14]

theorem c_logical_semantic : AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC ops = AspisR1CurrentCaller.PCVK_C.compact.LOGICAL_SEMANTIC := by
  unfold AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC
  exact b.h_op15

theorem c_off_folded_root : AspisR1CurrentCaller.compact.OFF_FOLDED_ROOT ops = AspisR1CurrentCaller.PCVK_C.compact.OFF_FOLDED_ROOT := by
  unfold AspisR1CurrentCaller.compact.OFF_FOLDED_ROOT AspisR1CurrentCaller.PCVK_C.compact.OFF_FOLDED_ROOT
  simp only [b.h_op21]

theorem c_off_round1 : AspisR1CurrentCaller.compact.OFF_ROUND1 ops = AspisR1CurrentCaller.PCVK_C.compact.OFF_ROUND1 := by
  unfold AspisR1CurrentCaller.compact.OFF_ROUND1 AspisR1CurrentCaller.PCVK_C.compact.OFF_ROUND1
  simp only [c_off_folded_root b]

theorem c_error_inst : AspisR1CurrentCaller.verifier.Error.Insts.CoreConvertFromCodecError ops = AspisR1CurrentCaller.PCVK_C.verifier.Error.Insts.CoreConvertFromCodecError := by
  unfold AspisR1CurrentCaller.verifier.Error.Insts.CoreConvertFromCodecError AspisR1CurrentCaller.PCVK_C.verifier.Error.Insts.CoreConvertFromCodecError
  rw [b.h_op2]


theorem verifier_candidate_prepare_eq (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare x H = @AspisR1CurrentCaller.verifier.candidate.prepare ops H := by
  funext aspis_coredigestDigest32Inst public1 proof hash obs g
  unfold AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare AspisR1CurrentCaller.verifier.candidate.prepare
  simp only [PRVEq_C_cp0, PRVEq_C_cp1, PRVEq_C_cp2, PRVEq_C_cp3, PRVEq_C_cp4, c_off_semantic b, c_off_y1 b, c_off_inactive b, c_logical_semantic b, c_off_folded_root b, c_off_round1 b, c_error_inst b, b.h_aspis_core_field_wide_exact_WideExact_ZERO, b.h_verifier_candidate_canonical_scan, b.h_verifier_QueryGeometry_for_range, b.h_verifier_candidate_batch_merkle, b.h_verifier_candidate_parse_shape, b.h_verifier_BatchedWeights_finish, b.h_verifier_candidate_query_loop, b.h_verifier_candidate_wide_view, b.h_r1_semantic_verify_observed, b.h_verifier_BatchedWeights_new, b.h_aspis_core_r0_heap_filled, b.h_verifier_Accumulator_new, b.h_compact_expand_semantic, b.h_verifier_Prepared_new, b.h_compact_expand_values, b.h_verifier_checkpoint, b.h_verifier_mark, bind_tc_ok]
  delta_matchers
  rfl

theorem verifier_candidate_tx1_eq (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.tx1 x H = @AspisR1CurrentCaller.verifier.candidate.tx1 ops H := by
  funext aspis_coredigestDigest32Inst public1 public_bytes proof k hash obs
  unfold AspisR1CurrentCaller.PCVK_C.verifier.candidate.tx1 AspisR1CurrentCaller.verifier.candidate.tx1
  simp only [PRVEq_C_cp0, PRVEq_C_cp1, PRVEq_C_cp2, PRVEq_C_cp3, PRVEq_C_cp4, c_off_semantic b, c_off_y1 b, c_off_inactive b, c_logical_semantic b, c_off_folded_root b, c_off_round1 b, c_error_inst b, verifier_candidate_prepare_eq b, b.h_aspis_core_field_wide_exact_WideExact_ZERO, b.h_verifier_candidate_canonical_scan, b.h_verifier_QueryGeometry_for_range, b.h_verifier_candidate_batch_merkle, b.h_verifier_candidate_parse_shape, b.h_verifier_BatchedWeights_finish, b.h_verifier_candidate_query_loop, b.h_verifier_candidate_wide_view, b.h_r1_semantic_verify_observed, b.h_verifier_BatchedWeights_new, b.h_aspis_core_r0_heap_filled, b.h_verifier_Accumulator_new, b.h_compact_expand_semantic, b.h_verifier_Prepared_new, b.h_compact_expand_values, b.h_verifier_checkpoint, b.h_verifier_mark, bind_tc_ok]
  delta_matchers
  rfl

end PRVEq.CallerPrepTx1_k1

namespace PRVEq.CallerPrepTx1_k1
open AspisR1CurrentCaller AspisR1CurrentCaller.PCVK_C
/-- Non-vacuity: for every ops0 there are ops (ops0 with the six constant/error fields set) and x with Bound ops x. -/
theorem bound_exists (ops0 : Ops) : ∃ ops : Ops, ∃ x : Ext, Bound ops x := by
  let ops : Ops := { ops0 with op2 := AspisR1CurrentCaller.PCVK_C.verifier.Error.Insts.CoreConvertFromCodecError.from, op12 := ok AspisR1CurrentCaller.PCVK_C.compact.OFF_SEMANTIC, op13 := AspisR1CurrentCaller.PCVK_C.compact.COMPACT_SEMANTIC, op14 := AspisR1CurrentCaller.PCVK_C.compact.COMPACT_Y1, op15 := AspisR1CurrentCaller.PCVK_C.compact.LOGICAL_SEMANTIC, op21 := AspisR1CurrentCaller.PCVK_C.compact.OFF_ROUND0 }
  exact ⟨ops, {
    aspis_core_field_wide_exact_WideExact_ZERO := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO ops
    verifier_candidate_canonical_scan := ops.op4
    verifier_QueryGeometry_for_range := ops.op19
    verifier_candidate_batch_merkle := @ops.op6
    verifier_candidate_parse_shape := ops.op3
    verifier_BatchedWeights_finish := ops.op17
    verifier_candidate_query_loop := ops.op7
    verifier_candidate_wide_view := ops.op5
    r1_semantic_verify_observed := @ops.op9
    verifier_BatchedWeights_new := ops.op18
    aspis_core_r0_heap_filled := @ops.op1
    verifier_Accumulator_new := ops.op20
    compact_expand_semantic := ops.op10
    verifier_Prepared_new := @ops.op8
    compact_expand_values := ops.op11
    verifier_checkpoint := @ops.op16
    verifier_mark := AspisR1CurrentCaller.verifier.mark
    }, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
end PRVEq.CallerPrepTx1_k1

#print axioms PRVEq.CallerPrepTx1_k1.c_off_semantic
#print axioms PRVEq.CallerPrepTx1_k1.c_off_y1
#print axioms PRVEq.CallerPrepTx1_k1.c_off_inactive
#print axioms PRVEq.CallerPrepTx1_k1.c_logical_semantic
#print axioms PRVEq.CallerPrepTx1_k1.c_off_folded_root
#print axioms PRVEq.CallerPrepTx1_k1.c_off_round1
#print axioms PRVEq.CallerPrepTx1_k1.c_error_inst
#print axioms PRVEq.CallerPrepTx1_k1.verifier_candidate_prepare_eq
#print axioms PRVEq.CallerPrepTx1_k1.verifier_candidate_tx1_eq
#print axioms PRVEq.CallerPrepTx1_k1.bound_exists
