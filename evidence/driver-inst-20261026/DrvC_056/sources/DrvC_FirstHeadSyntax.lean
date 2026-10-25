import DrvC_FirstSyntax
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstHeadSyntax
open Aeneas Aeneas.Std Result
open DrvC_Installation
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult

open VTop_Stages in
def stageHead {F C : Type} (c : Configuration F C)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (k : Usize) :
    SdkC_Source.Code (core.result.Result (alloc.vec.Vec U8) VTop_Stages.verifier.Error) :=
  let effects := DrvC_Effects.effects c
  do
  let i ← effects.op16
  if k != i
  then pure (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse)
  else
    let r ← effects.op3 proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← effects.op4 proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        effects.op13 none AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed
        let we ← effects.op1
        let g := Array.repeat 29#usize we
        let (r2, g1) ←
          effects.op7 (digest c) semantic proof
            () none g
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          DrvC_FirstSyntax.stageTail c pub proof k val g1
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



open AspisR1CurrentCaller in
def sourceHead {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (k : Usize) :
    SdkC_Source.Code (core.result.Result (alloc.vec.Vec U8) AspisR1CurrentCaller.verifier.Error) :=
  let base := GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry
  let B := c.boundaries
  let std := c.std
  let ops := currentInstalled c
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
            (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () g)
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          DrvC_FirstSyntax.sourceTail c hashv pub proof k val g1
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



end AspisR1.DrvC_FirstHeadSyntax
end
