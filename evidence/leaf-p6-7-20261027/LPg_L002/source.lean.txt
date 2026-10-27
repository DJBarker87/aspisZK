import Aeneas

/-! Pure P6 association: native stage certificates are named in LPa_LEAVES.md.
They are evidence references, not Lean axioms. This module only proves the
iteration/fold transport; it cannot manufacture native source correspondence. -/
set_option autoImplicit false
namespace LPa

def stages {S : Type} (step : S → Nat → S) (initial : S) : Nat → S
  | 0 => initial
  | n+1 => step (stages step initial n) n

/-- Induction on the actual iteration bound, without concrete loop reduction. -/
theorem stages_fold {S : Type} (step : S → Nat → S) (initial : S) (n : Nat) :
    stages step initial n = (List.range n).foldl step initial := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stages, ih, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil]

theorem stages_all (p : Nat → Bool) (n : Nat) :
    stages (fun good i => good && p i) true n = (List.range n).all p := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stages, ih, List.range_succ, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true]

theorem stages_append {S : Type} (step : S → Nat → S) (initial : S) (n : Nat) :
    stages step initial (n+1) = step ((List.range n).foldl step initial) n := by
  rw [stages, stages_fold]

#print axioms stages_fold
#print axioms stages_all
#print axioms stages_append
end LPa
