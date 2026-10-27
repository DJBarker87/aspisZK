import LPa_Fold
open Aeneas Result
set_option autoImplicit false
namespace LPa

def stagesM {S : Type} (step : S → Nat → Result S) (initial : S) : Nat → Result S
  | 0 => ok initial
  | n+1 => do
    let state ← stagesM step initial n
    step state n

theorem stagesM_fold {S : Type} (step : S → Nat → Result S) (initial : S) (n : Nat) :
    stagesM step initial n = (List.range n).foldlM step initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stagesM, ih, List.range_succ, List.foldlM_append,
      List.foldlM_cons, List.foldlM_nil, bind_pure]

/-- A recursive loop over the actual list, retaining all fail/div outcomes. -/
def walkM {A S : Type} (step : S → A → Result S) : List A → S → Result S
  | [], initial => ok initial
  | a::xs, initial => do
    let next ← step initial a
    walkM step xs next

theorem walkM_fold {A S : Type} (step : S → A → Result S) (xs : List A) (initial : S) :
    walkM step xs initial = xs.foldlM step initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a xs ih => simp only [walkM, List.foldlM_cons, ih]
#print axioms stagesM_fold
#print axioms walkM_fold
end LPa
