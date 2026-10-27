import R1Z.PV_Canon_CheckedRound
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-- Proof-only monitored copies of the extracted recursion and entry.
Only the call of the monitored round replaces the original round. -/
def checked_rounds
  {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (point : Array aspis_core.field.QM31 10#usize)
  (running : aspis_core.field.QM31) (round : Std.Usize) (oracle : F) :
  Result ((core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) r1_wire.Error) × (host_wire.SemanticTranscript H)
    × (alloc.vec.Vec Std.U8))
  := do
  if round = 10#usize
  then
    let r ← OracleInst.evaluate oracle point
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let b ←
        core.cmp.PartialEq.ne.trait_default
          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 val running
      if b
      then
        ok (core.result.Result.Err r1_wire.Error.Terminal, transcript, output)
      else ok (core.result.Result.Ok (point, running), transcript, output)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
          (core.convert.FromSame r1_wire.Error) residual
      ok (r1, transcript, output)
  else
    let (r, transcript1, output1) ←
      checked_round aspis_coredigestDigest32Inst
        OracleInst transcript output point running round oracle
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (point1, running1) := val
      let i ← Aeneas.Std.lift (Std.Usize.wrapping_add round 1#usize)
      checked_rounds aspis_coredigestDigest32Inst
        OracleInst transcript1 output1 point1 running1 i oracle
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
          (core.convert.FromSame r1_wire.Error) residual
      ok (r1, transcript1, output1)
partial_fixpoint

/-- [aspis_r1_cost_probe::host_sumcheck::prove_sumcheck]:
    Source: 'crates/aspis-r1-cost-probe/src/host_sumcheck.rs', lines 58:4-65:5
    Visibility: public -/
def checked_prover
  {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (initial_claim : aspis_core.field.QM31) (oracle : T1) :
  Result ((core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) r1_wire.Error) × (host_wire.SemanticTranscript H)
    × (alloc.vec.Vec Std.U8))
  := do
  let q ← aspis_core.field.QM31.ZERO
  let a := Array.repeat 10#usize q
  checked_rounds aspis_coredigestDigest32Inst OracleInst
    transcript output a initial_claim 0#usize oracle


end R1Z.PV_Canon
