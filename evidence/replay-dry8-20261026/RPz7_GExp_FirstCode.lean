import RPz7_GExp_QueryBudget
import RPz7_SdkC_BatchSource
import RPz7_SdkD_First
import RPz7_Tx1Q_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_FirstCode
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect (Code)
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult

def installed (base : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) : Ops :=
  RowShape_InstalledSlots.verifierOps
    (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std

def writerCode (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) :
    Code (alloc.vec.Vec U8) := do
  let ck ← CheckpointBytes5Writer.writer
    (CheckpointBytes3Namespaces.toPrepared (Tx1Q_Carriers.prepared p))
    (CheckpointBytes3Namespaces.toAccumulator (Tx1Q_Carriers.accumulator a)) proof pub
  pure ⟨ck.val,ck.property⟩

def code (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
  (D : aspis_core.digest.Digest32 Unit)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
   :
  Code (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  :=
  let ops := installed base B std
  do
  if k != compact.SPLIT
  then pure (core.result.Result.Err verifier.Error.Parse)
  else
    let r ← ops.op3 proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← ops.op4 proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        verifier.mark none verifier.Phase.Parsed
        let we ← (aspis_core.field.wide_exact.WideExact.ZERO ops)
        let g := Array.repeat 29#usize we
        let (r2, g1) ←
          SdkD_PrepareLower.lower (SdkD_PrepareSource.code
            (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std D public1 proof () g)
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
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
              SdkC_BatchSource.currentCode hashv proof val folded_root
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              verifier.mark none (verifier.Phase.Merkle 0#usize)
              let r6 ← ops.op19 val.queries 0#usize k
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                let s1 := alloc.vec.Vec.deref val1.weights
                let r7 ← ops.op18 s1
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let r8 ←
                    ops.op7 proof val val1 g1 none val2 val3 k
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let (a, pending) := val4
                    let (s2, deref_mut_back) ←
                      lift (alloc.vec.Vec.deref_mut a.weights)
                    let s3 ← ops.op17 pending s2
                    let v := deref_mut_back s3
                    let bytes ←
                      writerCode val {a with weights := v} proof public_bytes
                    verifier.mark none verifier.Phase.CheckpointWrite
                    pure (core.result.Result.Ok bytes)
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

end AspisR1.GExp_FirstCode
end
