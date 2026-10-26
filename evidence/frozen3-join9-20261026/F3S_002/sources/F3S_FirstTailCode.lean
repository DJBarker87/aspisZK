import GExq_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_FirstTailCode
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect (Code)
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult

def code {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (public_bytes proof : Slice U8) (k : Usize) (p : verifier.Prepared)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Code (core.result.Result (alloc.vec.Vec U8) verifier.Error) :=
  let ops := GExp_FirstCode.installed base B std
  do
  let r3 ← ops.op20 transport.Variant.S2
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    verifier.mark none verifier.Phase.Prepare
    let i ← (compact.OFF_FOLDED_ROOT ops)
    let i1 ← (compact.OFF_ROUND1 ops)
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
      GExq_BatchSource.current D hash proof p folded_root
    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf4 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      verifier.mark none (verifier.Phase.Merkle 0#usize)
      let r6 ← ops.op19 p.queries 0#usize k
      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
      match cf5 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let s1 := alloc.vec.Vec.deref val1.weights
        let r7 ← ops.op18 s1
        let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
        match cf6 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ←
            ops.op7 proof p val1 scratch none val2 val3 k
          let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
          match cf7 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let (a, pending) := val4
            let (s2, deref_mut_back) ←
              lift (alloc.vec.Vec.deref_mut a.weights)
            let s3 ← ops.op17 pending s2
            let v := deref_mut_back s3
            let bytes ←
              writerCode p {a with weights := v} proof public_bytes
            verifier.mark none verifier.Phase.CheckpointWrite
            pure (core.result.Result.Ok bytes)
end AspisR1.F3S_FirstTailCode
end
