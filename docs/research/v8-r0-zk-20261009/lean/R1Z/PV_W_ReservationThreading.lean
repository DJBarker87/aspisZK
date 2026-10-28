import R1Z.PV_W_Reservation
import R1Z.PV_W_Enriched
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_ReservationThreading
open ProverRwFull PV_W_SourceSyntax PV_W_Reservation PV_W_Syntax PV_W_Threading
open Aeneas.Std
variable [ExternalTypes]
variable {W C : Type}

/-- Source erasure is the full emitted Result, with no successful-run guard.
This is source-syntax fidelity, not native purity of the selected callbacks. -/
theorem source_complete (dictionary : ExternalFuns)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) :
    (eval (sourceInterpreter dictionary) (reserve self statement nonce) ()).outcome =
      resultOutcome
        (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
          _ dictionary self statement nonce) := by
  rw [source_value,erase_reserve]

/-- Exact operational threading for the reified extracted reservation. Local
operation validity is still required; it is not a native-effect certificate. -/
theorem reservation_exact (ops : Interpreter Op W C Aeneas.Std.Error)
    (step : W → C → W → Prop)
    (leaves : ∀ {A : Type} (op : Op A), Valid step (ops op))
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) (w : W)
    (r : Run W C Aeneas.Std.Error (Bool × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore))
    (executed : Executes ops (reserve self statement nonce) w r) :
    (eval ops (reserve self statement nonce) w).outcome = r.outcome ∧
    (eval ops (reserve self statement nonce) w).calls = r.calls ∧
    (eval ops (reserve self statement nonce) w).world = r.world ∧
    Threaded step w r.calls r.world :=
  execution_exact ops step leaves executed

/-- Every interpreter run has a corresponding operational derivation; callers
need not assume the existence of a source execution certificate. -/
theorem reservation_constructed (ops : Interpreter Op W C Aeneas.Std.Error)
    (step : W → C → W → Prop)
    (leaves : ∀ {A : Type} (op : Op A), Valid step (ops op))
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) (w : W) :
    Executes ops (reserve self statement nonce) w (eval ops (reserve self statement nonce) w) ∧
    Threaded step w (eval ops (reserve self statement nonce) w).calls
      (eval ops (reserve self statement nonce) w).world :=
  ⟨execution_complete ops _ w,eval_valid ops step leaves _ w⟩

variable {O Fs Allocator Extra Tag : Type}
local notation "Full" => PV_W_Enriched.World O Fs Allocator Extra

/-- Project only proven-silent process steps. Tagged OS calls retain their
exact pre-world sequence. Filesystem and full observer payload binding to the
existing TrustBoundary.Observation remain separate installation obligations. -/
theorem reservation_projection
    (ops : Interpreter Op Full (Option Tag) Aeneas.Std.Error)
    (fullStep : Full → Option Tag → Full → Prop) (osStep : O → Tag → O → Prop)
    (leaves : ∀ {A : Type} (op : Op A), Valid fullStep (ops op))
    (silent : ∀ w n, fullStep w none n → w.os = n.os)
    (visible : ∀ w n c, fullStep w (some c) n → osStep w.os c n.os)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) (w : Full) :
    Threaded osStep w.os
      (PV_W_Enriched.projectTrace PV_W_Enriched.World.os
        (eval ops (reserve self statement nonce) w).calls)
      (eval ops (reserve self statement nonce) w).world.os :=
  PV_W_Enriched.project_threaded PV_W_Enriched.World.os fullStep osStep silent visible
    (eval_valid ops fullStep leaves _ w)

#print axioms source_complete
#print axioms reservation_exact
#print axioms reservation_constructed
#print axioms reservation_projection
end R1Z.PV_W_ReservationThreading
