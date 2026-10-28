import R1Z.PV_RunJoin_WorldProjection33
import R1Z.PV_W_PrivateSaltsLoop
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LoopProjection33
open PV_W_Threading PV_W_Syntax PV_RunJoin_WorldProjection33 Aeneas.Std
variable {W V C D E S A : Type}

/-- The same loop fuel transports complete runs, including an unfinished
prefix. No termination claim or deletion of rejected iterations is used. -/
theorem fuel (world : W → V) (tag : C → D)
    (left : S → M W C E (ControlFlow S A))
    (right : S → M V D E (ControlFlow S A))
    (body : ∀ s w, project world tag (left s w) = right s (world w))
    (n : Nat) (s : S) (w : W) :
    project world tag (PV_W_Loops.fuel left n s w) =
      PV_W_Loops.fuel right n s (world w) := by
  induction n generalizing s w with
  | zero => rfl
  | succ n ih =>
    apply project_bind world tag (left s) (right s) _ _ (body s)
    intro cf nextWorld
    cases cf with
    | done a => rfl
    | cont next => exact ih next nextWorld

/-- Operational finite executions inherit the identical mapped run. This
uses pv-world's finite execution law rather than reimplementing a loop. -/
theorem finite (world : W → V) (tag : C → D)
    (left : S → M W C E (ControlFlow S A))
    (right : S → M V D E (ControlFlow S A))
    (body : ∀ s w, project world tag (left s w) = right s (world w))
    (s : S) (w : W) (r : Run W C E A)
    (exec : PV_W_Loops.Executes left s w r) :
    ∃ n, PV_W_Loops.fuel right n s (world w) = project world tag r := by
  obtain ⟨n,hn⟩ := PV_W_Loops.finite_exact left exec
  refine ⟨n,?_⟩
  rw [← fuel world tag left right body n s w,hn]

variable [ProverRwFull.ExternalTypes]
open ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
/-- Concrete recursive private-salt body, at its actual counter and Result
accumulator. Native/model leaf agreement remains an explicit P law. -/
theorem private_salts (world : W → V) (tag : C → D)
    (left : Interpreter Op W C Aeneas.Std.Error)
    (right : Interpreter Op V D Aeneas.Std.Error)
    (local_law : ∀ {B : Type} (op : Op B) w,
      project world tag (left op w) = right op (world w))
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (hash : Hash) (saltTag : U8) (count : Usize)
    (s : PV_W_PrivateSaltsLoop.State) (w : W) (n : Nat) :
    project world tag (PV_W_Loops.fuel
      (fun state => eval left (PV_W_PrivateSaltsLoop.body reserved context hash saltTag count state)) n s w) =
    PV_W_Loops.fuel
      (fun state => eval right (PV_W_PrivateSaltsLoop.body reserved context hash saltTag count state)) n s (world w) := by
  apply fuel world tag _ _
  intro state nextWorld
  exact eval_project world tag left right local_law _ nextWorld

#print axioms fuel
#print axioms finite
#print axioms private_salts
end R1Z.PV_RunJoin_LoopProjection33
