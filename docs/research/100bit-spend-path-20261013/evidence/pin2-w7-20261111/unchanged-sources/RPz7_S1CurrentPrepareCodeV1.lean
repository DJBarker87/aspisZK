import RPz7_S1SemanticCurrentCodeV1
import RPz7_S1ClosedPreparationHashCodeV1
import RPz7_S1NativePrepareBuffersV1
import S1ValuesOwnedInstallationV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.S1PrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisS1ValuesOwnedInstallation

def prepare (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (proof : Slice Std.U8) (hash : H)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  Code ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 29#usize))
  := do
  let ops := BorrowedClaimPrepared.NativeBuffers.install (withValues base) nativeValues R B

  let i ← (compact.LOGICAL_SEMANTIC ops)
  let i1 ← compact.LOGICAL_Y1
  let i2 ← i + i1
  let r ← ops.op1 core.marker.CopyU8 i2 0#u8
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
    let i3 ← (compact.OFF_SEMANTIC ops)
    let i4 ← (compact.OFF_Y1 ops)
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) proof { start := i3, «end» := i4 }
    let (r2, semantic1) ← ops.op10 s1 semantic
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let i5 ← (compact.OFF_INACTIVE ops)
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i4, «end» := i5 }
      let (r3, y11) ← ops.op11 s2 y1
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
        let r4 ← ops.op5 proof s4 s5
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue v =>
          let r5 ←
            S1SemanticCodeInstallation.code R B aspis_coredigestDigest32Inst public1
              v.semantic hash
          let r6 ←
            core.result.Result.map_err
              (verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
              aspis_coredigestDigest32Inst) r5 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r6
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            verifier.mark none verifier.Phase.Semantic
            BorrowedClaimPrepared.closedPreparationCode aspis_coredigestDigest32Inst val2 v hash g
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r7 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                verifier.Prepared (core.convert.FromSame verifier.Error)
                residual
            pure (r7, g)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r5 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              verifier.Prepared (core.convert.FromSame verifier.Error) residual
          pure (r5, g)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.Prepared (verifier.Error.Insts.CoreConvertFromCodecError ops)
            residual
        pure (r4, g)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared (verifier.Error.Insts.CoreConvertFromCodecError ops)
          residual
      pure (r3, g)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.Prepared (core.convert.FromSame verifier.Error) residual
    pure (r2, g)

#print axioms prepare
end AspisR1CurrentCaller.S1PrepareCode
