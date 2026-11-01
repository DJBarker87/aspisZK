import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_ProveSemantics
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  prepare_opening_OPEN : ∀ (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn), P ((core.result.Result prover.PreparedOpening verifier.Error))
  derive_private_salts_OPEN : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8), P ((core.result.Result host_commitment.PrivateSalts verifier.Error))
  finish_opening_OPEN : ∀ (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts), P ((core.result.Result prover.Publication verifier.Error))
  publish_compact_OPEN : ∀ (variant : transport.Variant) (p : prover.Publication), P ((core.result.Result (alloc.vec.Vec Std.U8) verifier.Error))

structure Compatible (c : Callees) : Prop where
  prepare_opening_fixed : ∀ (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn), FinishedView (c.prepare_opening_OPEN variant hash backend sem) (prover.prepare_opening variant hash backend sem)
  derive_private_salts_fixed : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8), FinishedView (c.derive_private_salts_OPEN reserved context hash tag) (prover.derive_private_salts reserved context hash tag)
  finish_opening_fixed : ∀ (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts), FinishedView (c.finish_opening_OPEN variant hash prepared folded_salts) (prover.finish_opening variant hash prepared folded_salts)
  publish_compact_fixed : ∀ (variant : transport.Variant) (p : prover.Publication), FinishedView (c.publish_compact_OPEN variant p) (prover.publish_compact variant p)

def run
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)) (c : Callees) : P (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error) := do
  let (reserved, context) := salts
  let r ← c.prepare_opening_OPEN variant hash backend sem
  let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← c.derive_private_salts_OPEN reserved context hash 114#u8
    let cf1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ← c.finish_opening_OPEN variant hash val val1
      let cf2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        c.publish_compact_OPEN variant val2
      | core.ops.control_flow.ControlFlow.Break residual =>
        PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual)

theorem run_fixed
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)) (c : Callees) (compatible : Compatible c) :
    FinishedView (run public1 variant hash backend sem salts c) (prover.prove_from_semantics public1 variant hash backend sem salts) := by
  unfold run prover.prove_from_semantics
  let (reserved, context) := salts
  try dsimp only
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact compatible.prepare_opening_fixed _ _ _ _
  · intro r
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact PV_EVH_Prefix.lift_fixed _
    · intro cf
      try dsimp only
      cases cf with
      | Continue val =>
        try dsimp only
        apply PV_EVH_Prefix.bind_fixed
        ·
          exact compatible.derive_private_salts_fixed _ _ _ _
        · intro r1
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact PV_EVH_Prefix.lift_fixed _
          · intro cf1
            try dsimp only
            cases cf1 with
            | Continue val1 =>
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed
              ·
                exact compatible.finish_opening_fixed _ _ _ _
              · intro r2
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact PV_EVH_Prefix.lift_fixed _
                · intro cf2
                  try dsimp only
                  cases cf2 with
                  | Continue val2 =>
                    exact compatible.publish_compact_fixed _ _
                  | Break residual =>
                    exact PV_EVH_Prefix.lift_fixed _
            | Break residual =>
              exact PV_EVH_Prefix.lift_fixed _
      | Break residual =>
        exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_ProveSemantics
