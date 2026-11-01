import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_PrivateSalts
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  FIBRE_COUNT_OPEN : P (Std.Usize)
  op32_OPEN : ∀ {T : Type} (A : Type) (arg0 : (alloc.vec.Vec T)) (arg1 : Std.Usize), P (((core.result.Result Unit alloc.collections.TryReserveError) × (alloc.vec.Vec T)))
  derive_private_salts_loop_OPEN : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize), P ((core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error))

structure Compatible (c : Callees) : Prop where
  FIBRE_COUNT_fixed : FinishedView (c.FIBRE_COUNT_OPEN) (aspis_core.r0.FIBRE_COUNT)
  op32_fixed : ∀ {T : Type} (A : Type) (arg0 : (alloc.vec.Vec T)) (arg1 : Std.Usize), FinishedView (c.op32_OPEN A arg0 arg1) (alloc.vec.Vec.try_reserve_exact A arg0 arg1)
  derive_private_salts_loop_fixed : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize), FinishedView (c.derive_private_salts_loop_OPEN reserved context hash tag count result index) (prover.derive_private_salts_loop reserved context hash tag count result index)

def run
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (c : Callees) : P (core.result.Result host_commitment.PrivateSalts verifier.Error) := do
  let count ← c.FIBRE_COUNT_OPEN
  let (r, salts) ← c.op32_OPEN Global (alloc.vec.Vec.new (Array Std.U8
      32#usize)) count
  let r1 ← PV_EVH_Prefix.lift (core.result.Result.map_err
      prover.derive_private_salts.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
      r ())
  let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let result ← c.derive_private_salts_loop_OPEN reserved context hash tag count
        (core.result.Result.Ok salts) 0#usize
    PV_EVH_Prefix.lift (core.result.Result.map (BuiltinFnOnce (alloc.vec.Vec (Array Std.U8
      32#usize)) host_commitment.PrivateSalts) result
      (host_commitment.PrivateSalts.new))
  | core.ops.control_flow.ControlFlow.Break residual =>
    PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      host_commitment.PrivateSalts (core.convert.FromSame verifier.Error)
      residual)

theorem run_fixed
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (c : Callees) (compatible : Compatible c) :
    FinishedView (run reserved context hash tag c) (prover.derive_private_salts reserved context hash tag) := by
  unfold run prover.derive_private_salts
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact compatible.FIBRE_COUNT_fixed
  · intro count
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact compatible.op32_fixed _ _ _
    · rintro ⟨r, salts⟩
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact PV_EVH_Prefix.lift_fixed _
      · intro r1
        try dsimp only
        apply PV_EVH_Prefix.bind_fixed
        ·
          exact PV_EVH_Prefix.lift_fixed _
        · intro cf
          try dsimp only
          cases cf with
          | Continue unused0 =>
            try dsimp only
            apply PV_EVH_Prefix.bind_fixed
            ·
              exact compatible.derive_private_salts_loop_fixed _ _ _ _ _ _ _
            · intro result
              exact PV_EVH_Prefix.lift_fixed _
          | Break residual =>
            exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_PrivateSalts
