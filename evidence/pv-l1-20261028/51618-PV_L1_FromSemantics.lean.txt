import PV_L1_Logged
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_FromSemantics
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Literal source caller with phase-entry instrumentation. Nested leaf
payloads are separate obligations; no arbitrary event callback occurs here. -/
def produce
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice U8) → Result (Array U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
    aspis_core.state_only_hiding.StateOnlyHidingContext) :
  Logged (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
  let (reserved,context) := salts
  let r ← observe .opening 0 (prover.prepare_opening variant hash backend sem)
  let cf ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | .Continue val =>
    let r1 ← observe .saltDerivation 2 (prover.derive_private_salts reserved context hash 114#u8)
    let cf1 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | .Continue val1 =>
      let r2 ← observe .opening 1 (prover.finish_opening variant hash val val1)
      let cf2 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | .Continue val2 => observe .publication 0 (prover.publish_compact variant val2)
      | .Break residual => PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
    | .Break residual => PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
  | .Break residual => PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)

theorem complete_result
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice U8) → Result (Array U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
    aspis_core.state_only_hiding.StateOnlyHidingContext) :
  erase (produce public1 variant hash backend sem salts) =
    prover.prove_from_semantics public1 variant hash backend sem salts := by
  rcases salts with ⟨reserved,context⟩
  unfold produce prover.prove_from_semantics
  simp only [erase_bind,erase_observe,erase_lift]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift]
#print axioms complete_result
end PV_L1_FromSemantics
