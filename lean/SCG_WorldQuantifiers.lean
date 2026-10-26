import SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_WorldQuantifiers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

abbrev zero : State := fun _ => 0
abbrev one : State := fun _ => 1

def fixed {A : Type} (i : A) : Program Bytes State A := .ask [] (fun _ => .done i)
def switched {A : Type} (i j : A) : Program Bytes State A :=
  .ask [] (fun s => .done (if s 0 = 0 then i else j))

/-- Fixed-world observations do not determine the adversary's selected inputs
in every world. This is a quantifier diagnostic, not a deployed attack. -/
theorem worlds {A : Type} (i j : A) (different : i ≠ j) :
    eval (fun _ => zero) (fixed i) = eval (fun _ => zero) (switched i j) ∧
    (eval (fun _ => one) (fixed i)).2 ≠ (eval (fun _ => one) (switched i j)).2 := by
  constructor
  · rfl
  · simpa only [fixed,switched,eval,one,show (1 : Fin 256) ≠ 0 by decide,if_false] using different

/-- Every predicate on the original selected native input is preserved in the
observed world, while the second world can select an unrelated native input. -/
theorem observations {A : Type} (i j : A) (R : A → Prop) :
    R (eval (fun _ => zero) (fixed i)).2 ↔ R (eval (fun _ => zero) (switched i j)).2 := by
  rfl

#print axioms worlds
#print axioms observations
end AspisR1.SCG_WorldQuantifiers
end
