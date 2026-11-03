import PV_EVH_Runtime
import PV_EVHB_CallbackEffects
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_PrivateSalts
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Runtime (Q PartialView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  drop_OPEN : ∀ {T : Type}, T → Q Unit
  FIBRE_COUNT_OPEN : Q (Std.Usize)
  op32_OPEN : ∀ {T : Type} (A : Type) (arg0 : (alloc.vec.Vec T)) (arg1 : Std.Usize), Q (((core.result.Result Unit alloc.collections.TryReserveError) × (alloc.vec.Vec T)))

  derive_private_salts_loop_OPEN : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize), Q ((core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error))
  op11_OPEN : ∀ {T : Type} {E : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
      core.ops.function.FnOnce F T U) (arg0 : (core.result.Result T E)) (arg1 : F), Q ((core.result.Result U E))

structure Compatible (c : Callees) : Prop where
  drop_fixed : ∀ {T : Type} (value : T), PartialView (c.drop_OPEN value) (.ok ())
  FIBRE_COUNT_fixed : PartialView (c.FIBRE_COUNT_OPEN) (aspis_core.r0.FIBRE_COUNT)
  op32_fixed : ∀ {T : Type} (A : Type) (arg0 : (alloc.vec.Vec T)) (arg1 : Std.Usize), PartialView (c.op32_OPEN A arg0 arg1) (alloc.vec.Vec.try_reserve_exact A arg0 arg1)

  derive_private_salts_loop_fixed : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize), PartialView (c.derive_private_salts_loop_OPEN reserved context hash tag count result index) (prover.derive_private_salts_loop reserved context hash tag count result index)
  op11_fixed : ∀ {T : Type} {E : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
      core.ops.function.FnOnce F T U) (arg0 : (core.result.Result T E)) (arg1 : F), PartialView (c.op11_OPEN opsfunctionFnOnceFTupleTUInst arg0 arg1) (core.result.Result.map opsfunctionFnOnceFTupleTUInst arg0 arg1)

def run
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (c : Callees) : Q (core.result.Result host_commitment.PrivateSalts verifier.Error) := do
  let count ← c.FIBRE_COUNT_OPEN
  let (r, salts) ← c.op32_OPEN Global (alloc.vec.Vec.new (Array Std.U8
      32#usize)) count
  let r1 ← PV_EVHB_CallbackEffects.mapErr c.drop_OPEN c.drop_OPEN verifier.Error.Allocation r ()
  let cf ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let result ← c.derive_private_salts_loop_OPEN reserved context hash tag count
        (core.result.Result.Ok salts) 0#usize
    c.op11_OPEN (BuiltinFnOnce (alloc.vec.Vec (Array Std.U8
      32#usize)) host_commitment.PrivateSalts) result
      (host_commitment.PrivateSalts.new)
  | core.ops.control_flow.ControlFlow.Break residual =>
    PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      host_commitment.PrivateSalts (core.convert.FromSame verifier.Error)
      residual)

theorem run_fixed
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (c : Callees) (compatible : Compatible c) :
    PartialView (run reserved context hash tag c) (prover.derive_private_salts reserved context hash tag) := by
  unfold run prover.derive_private_salts
  try dsimp only
  apply PV_EVH_Runtime.bind_view
  ·
    exact compatible.FIBRE_COUNT_fixed
  · intro count
    try dsimp only
    apply PV_EVH_Runtime.bind_view
    ·
      exact compatible.op32_fixed _ _ _
    · rintro ⟨r, salts⟩
      try dsimp only
      apply PV_EVH_Runtime.bind_view
      ·
        exact PV_EVHB_CallbackEffects.mapErr_view c.drop_OPEN c.drop_OPEN verifier.Error.Allocation () _
          (fun e => compatible.drop_fixed e) (compatible.drop_fixed ())
      · intro r1
        try dsimp only
        apply PV_EVH_Runtime.bind_view
        ·
          exact PV_EVH_Runtime.lift_view _
        · intro cf
          try dsimp only
          cases cf with
          | Continue unused0 =>
            try dsimp only
            apply PV_EVH_Runtime.bind_view
            ·
              exact compatible.derive_private_salts_loop_fixed _ _ _ _ _ _ _
            · intro result
              exact compatible.op11_fixed _ _ _
          | Break residual =>
            exact PV_EVH_Runtime.lift_view _

#print axioms run_fixed
end PV_EVHB_PrivateSalts
