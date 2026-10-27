import R1Z.ProverRwQueryOpening
/-! Exact emitted caller with its proved query component installed. Generated
by tools/prover-rw-20261023/query-composition.py; no native source change. -/
set_option autoImplicit false
namespace R1Z.ProverRwQuerySemantics
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def semantics
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  let (reserved, context) := salts
  let r ← prover.prepare_opening variant hash backend sem
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← prover.derive_private_salts reserved context hash 114#u8
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ← ProverRwQueryOpening.opening variant hash val val1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        prover.publish_compact variant val2
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

set_option backward.isDefEq.respectTransparency false in
theorem semantics_exact (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (h : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (salts : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
      aspis_core.state_only_hiding.StateOnlyHidingContext) :
    prover.prove_from_semantics pub variant h backend sem salts = semantics pub variant h backend sem salts := by
  simp only [prover.prove_from_semantics,semantics,ProverRwQueryOpening.opening_exact]
  try rfl

#print axioms semantics_exact
end R1Z.ProverRwQuerySemantics
