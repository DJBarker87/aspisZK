import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix067
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : prover.Backend) (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (d : Array aspis_core.field.QM31 1024#usize) (out : Payload (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0
      self columns 0#usize)) : Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    prover.Backend) := do
  let self1 := out
  let self2 ←
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1
      self1 d 0#usize
  let (o, o1) := core.option.Option.take self2.c1_salts
  let r ← core.option.Option.ok_or o r1_wire.Error.Public
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref self2.messages
    let r1 ←
      host_commitment.Commitment.new_salted self2.hash self2.domain
        host_commitment.CommitmentTime.C1 s self2.variant val
    let r2 ←
      core.result.Result.map_err
        prover.CommitmentsBackend.c1.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let root ← host_commitment.Commitment.root val1
      ok (core.result.Result.Ok root,
        { self2 with c1 := (some val1), c1_salts := o1 })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array Std.U8 32#usize) (core.convert.FromSame r1_wire.Error)
          residual
      ok (r3, { self2 with c1_salts := o1 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U8 32#usize) (core.convert.FromSame r1_wire.Error) residual
    ok (r1, { self2 with c1_salts := o1 })


end R1Z.PV_RE_ComposedSuffix067
pv_composed_source_contexts ProverRwFull.prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix067.continueAfter
