import XRz_HybridPrepared
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
noncomputable section
namespace XRz_HybridPrepare
def prepare (low : XRz_HybridSampler.Low)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (proof : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit))
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  Result ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 29#usize))
  := do
  let i ← _root_.XRn_Join_Release.compact.LOGICAL_SEMANTIC
  let i1 ← _root_.XRn_Join_Release.compact.LOGICAL_Y1
  let i2 ← i + i1
  let r ← aspis_core.r0.heap.filled core.marker.CopyU8 i2 0#u8
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
    let i3 ← _root_.XRn_Join_Release.compact.OFF_Y1
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) proof { start := _root_.XRn_Join_Release.compact.OFF_SEMANTIC, «end» := i3 }
    let (r2, semantic1) ← _root_.XRn_Join_Release.compact.expand_semantic s1 semantic
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let i4 ← _root_.XRn_Join_Release.compact.OFF_INACTIVE
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i3, «end» := i4 }
      let (r3, y11) ← _root_.compact.expand_values s2 y1
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
        let r4 ← verifier.candidate.wide_view proof s4 s5
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue v =>
          let r5 ←
            r1_semantic.verify_observed aspis_coredigestDigest32Inst public1
              v.semantic hash obs
          let r6 ←
            core.result.Result.map_err
              (verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
              aspis_coredigestDigest32Inst) r5 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r6
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            verifier.mark obs verifier.Phase.Semantic
            XRz_HybridPrepared.prepared low aspis_coredigestDigest32Inst val2 v hash g
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

end XRz_HybridPrepare
