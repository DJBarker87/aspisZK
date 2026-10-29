import R1Z.PV_W_R_PrivateSaltsBody
import R1Z.PV_W_Loops
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_PrivateSaltsLoop
open Aeneas Aeneas.Std ProverRwFull PV_W_Syntax PV_W_Threading
open PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

abbrev State := (core.result.Result (alloc.vec.Vec (Array U8 32#usize)) verifier.Error) × Usize
abbrev Value := core.result.Result (alloc.vec.Vec (Array U8 32#usize)) verifier.Error

variable (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Hash) (tag : U8) (count : Usize)

def body (s : State) :=
  PV_W_R_PrivateSaltsBody.program reserved context hash tag count s.1 s.2

theorem body_source (ops : ExternalFuns) (s : State) :
    erase ops (body reserved context hash tag count s) =
      @prover.derive_private_salts_loop.body _ ops reserved context (sourceHash ops hash) tag count s.1 s.2 :=
  PV_W_R_PrivateSaltsBody.erase_program ops reserved context hash tag count s.1 s.2

/-- The actual frozen loop is obtained from the recursively translated body
under Result erasure. No concrete iteration or native memory effect is reduced. -/
theorem source_loop_function (ops : ExternalFuns) (s : State) :
    Aeneas.Std.loop (fun state => erase ops (body reserved context hash tag count state)) s =
      @prover.derive_private_salts_loop _ ops reserved context (sourceHash ops hash) tag count s.1 s.2 := by
  unfold prover.derive_private_salts_loop
  have bodies : (fun state => erase ops (body reserved context hash tag count state)) =
      (fun (state : State) => @prover.derive_private_salts_loop.body _ ops reserved context
        (sourceHash ops hash) tag count state.1 state.2) :=
    funext (body_source reserved context hash tag count ops)
  rw [bodies]

theorem finite_source (ops : ExternalFuns) (s : State) (result : Aeneas.Std.Result Value)
    (h : PV_W_Loops.SourceExecutes
      (fun state => erase ops (body reserved context hash tag count state)) s result) :
    @prover.derive_private_salts_loop _ ops reserved context (sourceHash ops hash) tag count s.1 s.2 = result := by
  rw [← source_loop_function reserved context hash tag count ops s]
  exact PV_W_Loops.source_loop _ h

variable {W C : Type}

theorem finite_world (ops : Interpreter Op W C Aeneas.Std.Error)
    (s : State) (w : W) (r : Run W C Aeneas.Std.Error Value)
    (h : PV_W_Loops.Executes (fun state => eval ops (body reserved context hash tag count state)) s w r) :
    ∃ n, PV_W_Loops.fuel (fun state => eval ops (body reserved context hash tag count state)) n s w = r :=
  PV_W_Loops.finite_exact _ h

/-- Terminating/error/nonreturning iteration prefixes retain all ordered
world steps; native termination and adequacy of remaining leaves are not assumed. -/
theorem world_threaded (ops : Interpreter Op W C Aeneas.Std.Error)
    (step : W → C → W → Prop)
    (laws : ∀ {A : Type} (op : Op A), Valid step (ops op))
    (s : State) (w : W) (r : Run W C Aeneas.Std.Error Value)
    (h : PV_W_Loops.Executes (fun state => eval ops (body reserved context hash tag count state)) s w r) :
    Threaded step w r.calls r.world :=
  PV_W_Loops.execution_threaded _ step (fun state => eval_valid ops step laws _) h

#print axioms body_source
#print axioms source_loop_function
#print axioms finite_source
#print axioms finite_world
#print axioms world_threaded
end R1Z.PV_W_PrivateSaltsLoop
