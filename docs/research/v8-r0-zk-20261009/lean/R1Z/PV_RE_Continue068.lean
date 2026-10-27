import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue068
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : prover.Backend) (h1 : Slice aspis_core.field.QM31) (g : Array aspis_core.field.QM31 1024#usize) (out : Payload (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
      self h1 0#usize)) : Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    prover.Backend) := do
  let self1 := out
  let self2 ←
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1
      self1 g 0#usize
  let (o, o1) := core.option.Option.take self2.c2_salts
  let r ← core.option.Option.ok_or o r1_wire.Error.Public
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref self2.messages
    let r1 ←
      host_commitment.Commitment.new_salted self2.hash self2.domain
        host_commitment.CommitmentTime.C2 s self2.variant val
    let r2 ←
      core.result.Result.map_err
        prover.CommitmentsBackend.c2.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let root ← host_commitment.Commitment.root val1
      ok (core.result.Result.Ok root,
        { self2 with c2 := (some val1), c2_salts := o1 })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array Std.U8 32#usize) (core.convert.FromSame r1_wire.Error)
          residual
      ok (r3, { self2 with c2_salts := o1 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U8 32#usize) (core.convert.FromSame r1_wire.Error) residual
    ok (r1, { self2 with c2_salts := o1 })

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : prover.Backend) (h1 : Slice aspis_core.field.QM31) (g : Array aspis_core.field.QM31 1024#usize) :
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 (self := self) (h1 := h1) (g := g) =
      (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
      self h1 0#usize >>= fun out => continueAfter (self := self) (h1 := h1) (g := g) out) := by
  rw [prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : prover.Backend) (h1 : Slice aspis_core.field.QM31) (g : Array aspis_core.field.QM31 1024#usize) (out : Payload (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
      self h1 0#usize))
    (h : (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
      self h1 0#usize) = .ok out) :
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 (self := self) (h1 := h1) (g := g) = continueAfter (self := self) (h1 := h1) (g := g) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : prover.Backend) (h1 : Slice aspis_core.field.QM31) (g : Array aspis_core.field.QM31 1024#usize) (e : Error)
    (h : (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
      self h1 0#usize) = .fail e) :
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 (self := self) (h1 := h1) (g := g) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : prover.Backend) (h1 : Slice aspis_core.field.QM31) (g : Array aspis_core.field.QM31 1024#usize)
    (h : (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
      self h1 0#usize) = .div) :
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 (self := self) (h1 := h1) (g := g) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue068
