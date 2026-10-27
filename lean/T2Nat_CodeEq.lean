import T2Nat_ResultEq
import CheckpointBytes5Effect
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_CodeEq
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes5Effect T2Nat_ResultEq

def EqRun {A : Type} (p q : Code A) : Prop :=
  ∀ {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) (before : Log),
    EqOk (run D hash p before) (run D hash q before)

theorem refl {A : Type} (p : Code A) : EqRun p p := fun _ _ _ => T2Nat_ResultEq.refl _

theorem lift {A : Type} {r s : Result A} (h : EqOk r s) :
    EqRun (liftResult r) (liftResult s) := by
  intro H D hash before
  rw [run_lift,run_lift]
  exact T2Nat_ResultEq.bind h (fun _ => T2Nat_ResultEq.refl _)

theorem bind {A B : Type} {p q : Code A} {k l : A → Code B}
    (same : EqRun p q) (next : ∀ a, EqRun (k a) (l a)) :
    EqRun (p >>= k) (q >>= l) := by
  intro H D hash before
  rw [run_bind,run_bind]
  apply T2Nat_ResultEq.bind (same D hash before)
  rintro ⟨a,after⟩
  exact next a D hash after

#print axioms refl
#print axioms lift
#print axioms bind
end AspisR1.T2Nat_CodeEq
end
